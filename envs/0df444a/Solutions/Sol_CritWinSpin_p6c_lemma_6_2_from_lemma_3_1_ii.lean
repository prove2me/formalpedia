-- Prove2me | solution 1 for CritWinSpin.p6c_lemma_6_2_from_lemma_3_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-16T02:30:35.560209+00:00
-- url     : https://prove2.me/submissions/0ebbb5c2-6ba0-4e2a-b010-1f7139f75e01

import Mathlib
import Definitions.Def_CritWinSpin_nuPm
import Definitions.Def_CritWinSpin_SpinLaw

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CritWinSpin

namespace P6c

section SpinBasics

private noncomputable def mgf (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))

private lemma mgf_pos (S : SpinLaw) (t : ℝ) : 0 < mgf S t := by
  unfold mgf
  have hmem : (1 : ℚ) ∈ S.A := S.one_mem
  have hterm : 0 < (S.ρ (1 : ℚ) : ℝ) * Real.exp (t * ((1 : ℚ) : ℝ)) := by
    have hρ : 0 < (S.ρ 1 : ℝ) := by exact_mod_cast S.pos 1 hmem
    positivity
  have hnonneg : ∀ x ∈ S.A, 0 ≤ (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
    intro x hx
    have hρ : 0 < (S.ρ x : ℝ) := by exact_mod_cast S.pos x hx
    positivity
  calc 0 < (S.ρ (1 : ℚ) : ℝ) * Real.exp (t * ((1 : ℚ) : ℝ)) := hterm
    _ ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) :=
        Finset.single_le_sum hnonneg hmem

private lemma mgf_zero (S : SpinLaw) : mgf S 0 = 1 := by
  unfold mgf
  simp only [zero_mul, Real.exp_zero, mul_one]
  exact_mod_cast S.sum_one

private lemma mgf_even (S : SpinLaw) (t : ℝ) : mgf S (-t) = mgf S t := by
  unfold mgf
  refine Finset.sum_equiv (Equiv.neg ℚ) ?_ ?_
  · intro x
    simp only [Equiv.neg_apply]
    constructor
    · intro hx
      exact S.neg_mem x hx
    · intro hx
      simpa using S.neg_mem (-x) hx
  · intro x hx
    simp only [Equiv.neg_apply, Rat.cast_neg]
    rw [S.symm x hx]
    ring_nf

private lemma phi_even (S : SpinLaw) (t : ℝ) : phi S (-t) = phi S t := by
  unfold phi
  change Real.log (mgf S (-t)) = Real.log (mgf S t)
  rw [mgf_even]

private lemma phi_zero (S : SpinLaw) : phi S 0 = 0 := by
  unfold phi
  change Real.log (mgf S 0) = 0
  rw [mgf_zero, Real.log_one]

private lemma phi_nonneg (S : SpinLaw) (t : ℝ) : 0 ≤ phi S t := by
  unfold phi
  have hge : 1 ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
    have h2 : ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) =
        (mgf S t + mgf S (-t)) / 2 := by
      rw [mgf_even]
      unfold mgf
      ring
    rw [h2]
    have hsum : (mgf S t + mgf S (-t)) / 2 =
        ∑ x ∈ S.A, (S.ρ x : ℝ) * ((Real.exp (t * (x : ℝ)) + Real.exp ((-t) * (x : ℝ))) / 2) := by
      unfold mgf
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro x _
      ring
    rw [hsum]
    have h1 : (1 : ℝ) = ∑ x ∈ S.A, (S.ρ x : ℝ) := by
      symm
      exact_mod_cast S.sum_one
    rw [h1]
    refine Finset.sum_le_sum ?_
    intro x hx
    have hρ : 0 ≤ (S.ρ x : ℝ) := by exact_mod_cast (S.pos x hx).le
    have he1 : t * (x : ℝ) + 1 ≤ Real.exp (t * (x : ℝ)) := Real.add_one_le_exp (t * (x : ℝ))
    have he2 : -(t * (x : ℝ)) + 1 ≤ Real.exp (-(t * (x : ℝ))) := Real.add_one_le_exp (-(t * (x : ℝ)))
    have he3 : (1 : ℝ) ≤ (Real.exp (t * (x : ℝ)) + Real.exp ((-t) * (x : ℝ))) / 2 := by
      have hneg : (-t) * (x : ℝ) = -(t * (x : ℝ)) := by ring
      rw [hneg]
      linarith
    exact le_mul_of_one_le_right hρ he3
  exact Real.log_nonneg hge

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
    refine ContDiff.sum fun x _ => ?_
    exact contDiff_const.mul ((contDiff_id.mul contDiff_const).exp)
  change ContDiff ℝ ⊤ (fun t => Real.log (mgf S t))
  exact hmgf.log (fun t => (mgf_pos S t).ne')

private lemma deriv_phi_neg (S : SpinLaw) (t : ℝ) : deriv (phi S) (-t) = - deriv (phi S) t := by
  have hcomp : HasDerivAt (fun s => phi S (-s)) (- deriv (phi S) (-t)) t :=
    ((hasDerivAt_phi S (-t)).comp t (hasDerivAt_id' t).neg).congr_deriv (by
      rw [← deriv_phi_eq S (-t)]; ring)
  have hev : (fun s => phi S (-s)) = phi S := funext (phi_even S)
  rw [hev] at hcomp
  have h := hcomp.deriv
  linarith

private lemma deriv_phi_zero (S : SpinLaw) : deriv (phi S) 0 = 0 := by
  have h := deriv_phi_neg S 0
  simp only [neg_zero] at h
  linarith

private lemma deriv_phi_bdd (S : SpinLaw) (t : ℝ) : |deriv (phi S) t| ≤ 1 := by
  rw [deriv_phi_eq, abs_div, abs_of_pos (mgf_pos S t), div_le_one (mgf_pos S t)]
  calc |∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))|
      ≤ ∑ x ∈ S.A, |(S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro x hx
        have hρ : 0 ≤ (S.ρ x : ℝ) := by exact_mod_cast (S.pos x hx).le
        have hx1 : |(x : ℝ)| ≤ 1 := by
          have := S.mem_Icc x hx
          rw [abs_le]
          constructor
          · exact_mod_cast this.1
          · exact_mod_cast this.2
        rw [abs_mul, abs_mul, abs_of_nonneg hρ, abs_of_pos (Real.exp_pos _)]
        calc (S.ρ x : ℝ) * |(x : ℝ)| * Real.exp (t * (x : ℝ))
            ≤ (S.ρ x : ℝ) * 1 * Real.exp (t * (x : ℝ)) := by
              gcongr
          _ = (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by ring

private lemma variance_pos (S : SpinLaw) : 0 < variance S := by
  unfold variance varQ
  have hmem : (1 : ℚ) ∈ S.A := S.one_mem
  have hnonneg : ∀ x ∈ S.A, 0 ≤ x ^ 2 * S.ρ x := by
    intro x hx
    exact mul_nonneg (sq_nonneg x) (S.pos x hx).le
  have hgt : (0 : ℚ) < ∑ x ∈ S.A, x ^ 2 * S.ρ x := by
    calc (0 : ℚ) < (1 : ℚ) ^ 2 * S.ρ 1 := by
          have := S.pos 1 hmem
          positivity
      _ ≤ ∑ x ∈ S.A, x ^ 2 * S.ρ x := Finset.single_le_sum hnonneg hmem
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
  push_cast
  field_simp [hv]

private lemma hasDerivAt_deriv_phi (S : SpinLaw) (t : ℝ) :
    HasDerivAt (deriv (phi S))
      (((∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) * mgf S t -
        (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) ^ 2) / (mgf S t) ^ 2) t := by
  let num : ℝ → ℝ := fun s => ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (s * (x : ℝ))
  have hnum : HasDerivAt num (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) t := by
    have hterm : ∀ x ∈ S.A,
        HasDerivAt (fun s : ℝ => (S.ρ x : ℝ) * (x : ℝ) * Real.exp (s * (x : ℝ)))
          ((S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) t := by
      intro x _
      have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * (x : ℝ)))
          (Real.exp (t * (x : ℝ)) * (x : ℝ)) t :=
        ((hasDerivAt_id' t).mul_const (x : ℝ)).exp.congr_deriv (by ring)
      exact (hexp.const_mul ((S.ρ x : ℝ) * (x : ℝ))).congr_deriv (by ring)
    exact HasDerivAt.fun_sum fun x hx => hterm x hx
  have hdiv := hnum.div (hasDerivAt_mgf S t) (mgf_pos S t).ne'
  refine (hdiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv
    (by dsimp [num]; ring)
  exact deriv_phi_eq S s

private lemma deriv2_phi_nonneg (S : SpinLaw) (t : ℝ) : 0 ≤ deriv (deriv (phi S)) t := by
  rw [(hasDerivAt_deriv_phi S t).deriv]
  refine div_nonneg ?_ (sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S.A
    (fun x => Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))))
    (fun x => (x : ℝ) * Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))))
  have hL : (∑ x ∈ S.A, Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) *
      ((x : ℝ) * Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))))) ^ 2 =
      (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) ^ 2 := by
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hnn : 0 ≤ (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
      have := (S.pos x hx).le
      positivity
    calc Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) *
          ((x : ℝ) * Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))))
        = (x : ℝ) * (Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) *
            Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ)))) := by ring
      _ = (x : ℝ) * ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) := by rw [Real.mul_self_sqrt hnn]
      _ = (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ)) := by ring
  have hR1 : ∑ x ∈ S.A, Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) ^ 2 = mgf S t := by
    unfold mgf
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hnn : 0 ≤ (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
      have := (S.pos x hx).le
      positivity
    exact Real.sq_sqrt hnn
  have hR2 : ∑ x ∈ S.A, ((x : ℝ) * Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ)))) ^ 2 =
      ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hnn : 0 ≤ (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
      have := (S.pos x hx).le
      positivity
    rw [mul_pow, Real.sq_sqrt hnn]
    ring
  rw [hL, hR1, hR2] at hcs
  linarith

private lemma deriv_phi_monotone (S : SpinLaw) : Monotone (deriv (phi S)) := by
  refine monotone_of_deriv_nonneg ?_ (deriv2_phi_nonneg S)
  rw [← iteratedDeriv_one (f := phi S)]
  exact (phi_contDiff S).differentiable_iteratedDeriv 1 (by simp)

private lemma iteratedDeriv2_phi_eq (S : SpinLaw) :
    iteratedDeriv 2 (phi S) = deriv (deriv (phi S)) := by
  funext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]

private lemma deriv2_phi_zero (S : SpinLaw) : deriv (deriv (phi S)) 0 = variance S := by
  rw [(hasDerivAt_deriv_phi S 0).deriv, mgf_zero]
  have h1 : ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (0 * (x : ℝ)) = 0 := by
    have he := deriv_phi_zero S
    rw [deriv_phi_eq, mgf_zero, div_one] at he
    exact he
  rw [h1]
  simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_one, one_pow, div_one,
    Real.exp_zero]
  unfold variance varQ
  push_cast
  refine Finset.sum_congr rfl ?_
  intro x _
  ring

private lemma phi_le_quad (S : SpinLaw) (hS : IsGHS S) (t : ℝ) :
    phi S t ≤ t ^ 2 / (2 * tau S) := by
  have hpos_nonneg : ∀ s : ℝ, 0 ≤ s → phi S s ≤ s ^ 2 / (2 * tau S) := by
    intro s hs
    have h2_anti : AntitoneOn (deriv (deriv (phi S))) (Set.Ici 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
      · exact ((phi_contDiff S).continuous_iteratedDeriv 2 le_top).continuousOn.congr
          (fun x _ => by simp [iteratedDeriv2_phi_eq])
      · refine fun x _ => ?_
        rw [← iteratedDeriv2_phi_eq S]
        exact ((phi_contDiff S).differentiable_iteratedDeriv 2
          (by exact_mod_cast (WithTop.coe_lt_top (2 : ℕ∞) : ((2 : ℕ∞) : WithTop ℕ∞) < ⊤)) x).differentiableWithinAt
      · intro x hx
        have hd : HasDerivAt (deriv (deriv (phi S))) (iteratedDeriv 3 (phi S) x) x := by
          rw [← iteratedDeriv2_phi_eq]
          have hd3 : DifferentiableAt ℝ (iteratedDeriv 2 (phi S)) x :=
            (phi_contDiff S).differentiable_iteratedDeriv 2
              (by exact_mod_cast (WithTop.coe_lt_top (2 : ℕ∞) : ((2 : ℕ∞) : WithTop ℕ∞) < ⊤)) x
          rw [iteratedDeriv_succ (n := 2) (f := phi S)]
          exact hd3.hasDerivAt
        rw [hd.deriv]
        exact hS x (interior_subset hx)
    have h2_le : ∀ x : ℝ, 0 ≤ x → deriv (deriv (phi S)) x ≤ variance S := by
      intro x hx
      have := h2_anti (Set.mem_Ici.mpr le_rfl) hx hx
      simpa [deriv2_phi_zero S] using this
    have h1_le : ∀ x : ℝ, 0 ≤ x → deriv (phi S) x ≤ variance S * x := by
      intro x hx
      let f : ℝ → ℝ := fun u => variance S * u - deriv (phi S) u
      have hf_mono : MonotoneOn f (Set.Ici 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
        · have hd_cont : Continuous (deriv (phi S)) := by
            rw [← iteratedDeriv_one (f := phi S)]
            exact (phi_contDiff S).continuous_iteratedDeriv 1 (by simp)
          exact ((continuous_const.mul continuous_id).sub hd_cont).continuousOn
        · intro u _
          have hd1 : DifferentiableAt ℝ (deriv (phi S)) u :=
            (hasDerivAt_deriv_phi S u).differentiableAt
          exact (((hasDerivAt_id' u).const_mul (variance S)).sub hd1.hasDerivAt).differentiableAt.differentiableWithinAt
        · intro u hu
          have hd1 := (hasDerivAt_deriv_phi S u).differentiableAt
          have hdf : HasDerivAt f (variance S - deriv (deriv (phi S)) u) u :=
            (((hasDerivAt_id' u).const_mul (variance S)).sub hd1.hasDerivAt).congr_deriv (by ring)
          rw [hdf.deriv]
          linarith [h2_le u (interior_subset hu)]
      have h0 : f 0 ≤ f x := hf_mono (Set.mem_Ici.mpr le_rfl) hx hx
      simp only [f, mul_zero, deriv_phi_zero S, sub_self] at h0
      linarith
    let g : ℝ → ℝ := fun u => (variance S / 2) * u ^ 2 - phi S u
    have hg_mono : MonotoneOn g (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
      · exact ((continuous_const.mul (continuous_pow 2)).sub (phi_contDiff S).continuous).continuousOn
      · intro u _
        have hdg : HasDerivAt g (variance S * u - deriv (phi S) u) u := by
          have hpow : HasDerivAt (fun v : ℝ => (variance S / 2) * v ^ 2) (variance S * u) u :=
            ((hasDerivAt_pow 2 u).const_mul (variance S / 2)).congr_deriv (by ring)
          exact hpow.sub (hasDerivAt_phi S u).differentiableAt.hasDerivAt
        exact hdg.differentiableAt.differentiableWithinAt
      · intro u hu
        have hdg : HasDerivAt g (variance S * u - deriv (phi S) u) u := by
          have hpow : HasDerivAt (fun v : ℝ => (variance S / 2) * v ^ 2) (variance S * u) u :=
            ((hasDerivAt_pow 2 u).const_mul (variance S / 2)).congr_deriv (by ring)
          exact hpow.sub (hasDerivAt_phi S u).differentiableAt.hasDerivAt
        rw [hdg.deriv]
        linarith [h1_le u (interior_subset hu)]
    have h0 : g 0 ≤ g s := hg_mono (Set.mem_Ici.mpr le_rfl) hs hs
    simp only [g, zero_pow (by norm_num : 2 ≠ 0), mul_zero, phi_zero S, sub_self] at h0
    have hinv : variance S / 2 = 1 / (2 * tau S) := by
      have ht := tau_mul_variance S
      have htp : tau S ≠ 0 := (tau_pos S).ne'
      field_simp [htp]
      linarith
    rw [hinv] at h0
    linarith [show (1 / (2 * tau S)) * s ^ 2 = s ^ 2 / (2 * tau S) by ring]
  rcases le_total 0 t with ht | ht
  · exact hpos_nonneg t ht
  · rw [← phi_even S t]
    have hnn : 0 ≤ -t := neg_nonneg.mpr ht
    simpa [neg_sq] using hpos_nonneg (-t) hnn

private lemma phi_ge_abs_sub_log (S : SpinLaw) (t : ℝ) :
    Real.log (S.ρ 1 : ℝ) + |t| ≤ phi S t := by
  have hρ1 : 0 < (S.ρ 1 : ℝ) := by exact_mod_cast S.pos 1 S.one_mem
  have hpos : ∀ s : ℝ, 0 ≤ s → Real.log (S.ρ 1 : ℝ) + s ≤ phi S s := by
    intro s _
    unfold phi
    have hle : (S.ρ 1 : ℝ) * Real.exp s ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (s * (x : ℝ)) := by
      have hnonneg : ∀ x ∈ S.A, 0 ≤ (S.ρ x : ℝ) * Real.exp (s * (x : ℝ)) := by
        intro x hx
        have hρ : 0 ≤ (S.ρ x : ℝ) := by exact_mod_cast (S.pos x hx).le
        positivity
      calc (S.ρ 1 : ℝ) * Real.exp s = (S.ρ 1 : ℝ) * Real.exp (s * ((1 : ℚ) : ℝ)) := by simp
        _ ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (s * (x : ℝ)) := Finset.single_le_sum hnonneg S.one_mem
    have hlog := Real.log_le_log (by positivity) hle
    rw [Real.log_mul hρ1.ne' (Real.exp_pos s).ne', Real.log_exp] at hlog
    exact hlog
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact hpos t ht
  · rw [abs_of_nonpos ht, ← phi_even S t]
    exact hpos (-t) (neg_nonneg.mpr ht)

private lemma rateI_bddAbove (S : SpinLaw) {m : ℝ} (hm : |m| ≤ 1) :
    BddAbove (Set.range (fun t : ℝ => t * m - phi S t)) := by
  refine ⟨-Real.log (S.ρ 1 : ℝ), ?_⟩
  rintro _ ⟨t, rfl⟩
  have h1 := phi_ge_abs_sub_log S t
  have htm : t * m ≤ |t| := by
    calc t * m ≤ |t * m| := le_abs_self _
      _ = |t| * |m| := abs_mul _ _
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hm (abs_nonneg t)
      _ = |t| := mul_one _
  linarith

private lemma rateI_zero (S : SpinLaw) : rateI S 0 = 0 := by
  unfold rateI
  refine le_antisymm ?_ ?_
  · refine ciSup_le ?_
    intro t
    have := phi_nonneg S t
    linarith
  · have hb := rateI_bddAbove S (by norm_num : |(0 : ℝ)| ≤ 1)
    calc (0 : ℝ) = 0 * 0 - phi S 0 := by rw [phi_zero]; ring
      _ ≤ ⨆ t : ℝ, (t * 0 - phi S t) := le_ciSup hb 0

private lemma rateI_ge_quad (S : SpinLaw) (hS : IsGHS S) {m : ℝ} (hm : |m| ≤ 1) :
    (tau S / 2) * m ^ 2 ≤ rateI S m := by
  unfold rateI
  have hb := rateI_bddAbove S hm
  have hle := le_ciSup hb (tau S * m)
  have hphi := phi_le_quad S hS (tau S * m)
  have htp : 0 < tau S := tau_pos S
  have hcalc : (tau S * m) * m - (tau S * m) ^ 2 / (2 * tau S) = (tau S / 2) * m ^ 2 := by
    field_simp [htp.ne']
    ring
  linarith

private lemma rateI_eq_at_deriv (S : SpinLaw) {t₀ u : ℝ} (hu : u = deriv (phi S) t₀)
    (hu_le : |u| ≤ 1) :
    rateI S u = t₀ * u - phi S t₀ := by
  unfold rateI
  have hb := rateI_bddAbove S hu_le
  refine le_antisymm ?_ (le_ciSup hb t₀)
  refine ciSup_le ?_
  intro t
  let f : ℝ → ℝ := fun s => s * u - phi S s
  have hf_deriv : ∀ s, HasDerivAt f (u - deriv (phi S) s) s :=
    fun s => (((hasDerivAt_id' s).mul_const u).sub (hasDerivAt_phi S s).differentiableAt.hasDerivAt).congr_deriv (by ring)
  rcases le_total t t₀ with ht | ht
  · have hmono : MonotoneOn f (Set.Iic t₀) := by
      refine monotoneOn_of_deriv_nonneg (convex_Iic t₀) ?_ ?_ ?_
      · exact ((continuous_id.mul continuous_const).sub (phi_contDiff S).continuous).continuousOn
      · exact fun s _ => (hf_deriv s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [(hf_deriv s).deriv, hu]
        have := deriv_phi_monotone S (@interior_subset ℝ _ (Set.Iic t₀) s hs)
        linarith
    exact hmono ht (Set.mem_Iic.mpr le_rfl) ht
  · have hanti : AntitoneOn f (Set.Ici t₀) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici t₀) ?_ ?_ ?_
      · exact ((continuous_id.mul continuous_const).sub (phi_contDiff S).continuous).continuousOn
      · exact fun s _ => (hf_deriv s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [(hf_deriv s).deriv, hu]
        have := deriv_phi_monotone S (@interior_subset ℝ _ (Set.Ici t₀) s hs)
        linarith
    exact hanti (Set.mem_Ici.mpr le_rfl) ht ht

private lemma deriv_phi_large (S : SpinLaw) :
    ∃ Tmax : ℝ, 0 < Tmax ∧ (1 / 2 : ℝ) ≤ deriv (phi S) Tmax := by
  let A' : Finset ℚ := S.A.erase 1
  have hA'ne : A'.Nonempty := by
    refine ⟨(-1 : ℚ), ?_⟩
    rw [Finset.mem_erase]
    exact ⟨by norm_num, S.neg_one_mem⟩
  let mtop : ℚ := A'.max' hA'ne
  have hmtop_mem : mtop ∈ A' := Finset.max'_mem A' hA'ne
  have hmtop_lt : (mtop : ℝ) < 1 := by
    have hmemA := Finset.mem_of_mem_erase hmtop_mem
    have hne1 : mtop ≠ 1 := (Finset.mem_erase.mp hmtop_mem).1
    have hle1 : mtop ≤ 1 := (S.mem_Icc mtop hmemA).2
    have hlt : mtop < 1 := lt_of_le_of_ne hle1 hne1
    exact_mod_cast hlt
  let d : ℝ := 1 - (mtop : ℝ)
  have hd : 0 < d := by linarith
  have hρ1 : 0 < (S.ρ 1 : ℝ) := by exact_mod_cast S.pos 1 S.one_mem
  let Tmax : ℝ := max 1 ((Real.log (4 / (S.ρ 1 : ℝ)) + 1) / d)
  refine ⟨Tmax, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  have hT_nonneg : 0 ≤ Tmax := (lt_of_lt_of_le one_pos (le_max_left _ _)).le
  have hdiff : 1 - deriv (phi S) Tmax =
      (∑ x ∈ S.A, (S.ρ x : ℝ) * (1 - (x : ℝ)) * Real.exp (Tmax * (x : ℝ))) / mgf S Tmax := by
    rw [deriv_phi_eq]
    have hmgf_pos := (mgf_pos S Tmax).ne'
    have hmgf_eq : mgf S Tmax = ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (Tmax * (x : ℝ)) := rfl
    rw [one_sub_div hmgf_pos, hmgf_eq, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  have hnum_le : ∑ x ∈ S.A, (S.ρ x : ℝ) * (1 - (x : ℝ)) * Real.exp (Tmax * (x : ℝ)) ≤
      2 * Real.exp (Tmax * (mtop : ℝ)) := by
    have hsplit : ∑ x ∈ S.A, (S.ρ x : ℝ) * (1 - (x : ℝ)) * Real.exp (Tmax * (x : ℝ)) =
        ∑ x ∈ A', (S.ρ x : ℝ) * (1 - (x : ℝ)) * Real.exp (Tmax * (x : ℝ)) := by
      rw [← Finset.add_sum_erase S.A _ S.one_mem]
      simp [A']
    rw [hsplit]
    calc ∑ x ∈ A', (S.ρ x : ℝ) * (1 - (x : ℝ)) * Real.exp (Tmax * (x : ℝ))
        ≤ ∑ x ∈ A', (S.ρ x : ℝ) * 2 * Real.exp (Tmax * (mtop : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          have hxA := Finset.mem_of_mem_erase hx
          have hρ : 0 ≤ (S.ρ x : ℝ) := by exact_mod_cast (S.pos x hxA).le
          have h1x : 0 ≤ 1 - (x : ℝ) := by
            have := (S.mem_Icc x hxA).2
            linarith [show (x : ℝ) ≤ 1 by exact_mod_cast this]
          have h1x_le : 1 - (x : ℝ) ≤ 2 := by
            have := (S.mem_Icc x hxA).1
            linarith [show (-1 : ℝ) ≤ (x : ℝ) by exact_mod_cast this]
          have hx_le : (x : ℝ) ≤ (mtop : ℝ) := by
            exact_mod_cast Finset.le_max' A' x hx
          have hexp : Real.exp (Tmax * (x : ℝ)) ≤ Real.exp (Tmax * (mtop : ℝ)) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx_le hT_nonneg)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1x_le hρ) hexp (Real.exp_pos _).le (by positivity)
      _ = (∑ x ∈ A', (S.ρ x : ℝ)) * (2 * Real.exp (Tmax * (mtop : ℝ))) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
      _ ≤ 1 * (2 * Real.exp (Tmax * (mtop : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hleA : ∑ x ∈ A', (S.ρ x : ℝ) ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
            intro x hx _
            exact_mod_cast (S.pos x hx).le
          have hsum1 : ∑ x ∈ S.A, (S.ρ x : ℝ) = 1 := by exact_mod_cast S.sum_one
          linarith
      _ = 2 * Real.exp (Tmax * (mtop : ℝ)) := one_mul _
  have hden_ge : (S.ρ 1 : ℝ) * Real.exp Tmax ≤ mgf S Tmax := by
    unfold mgf
    have hnonneg : ∀ x ∈ S.A, 0 ≤ (S.ρ x : ℝ) * Real.exp (Tmax * (x : ℝ)) := by
      intro x hx
      have := (S.pos x hx).le
      positivity
    calc (S.ρ 1 : ℝ) * Real.exp Tmax = (S.ρ 1 : ℝ) * Real.exp (Tmax * ((1 : ℚ) : ℝ)) := by simp
      _ ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (Tmax * (x : ℝ)) :=
          Finset.single_le_sum hnonneg S.one_mem
  have hT_bound : Real.log (4 / (S.ρ 1 : ℝ)) + 1 ≤ d * Tmax := by
    have hle : (Real.log (4 / (S.ρ 1 : ℝ)) + 1) / d ≤ Tmax := le_max_right _ _
    have := mul_le_mul_of_nonneg_left hle hd.le
    rw [mul_div_cancel₀ _ hd.ne'] at this
    exact this
  have hexp_bound : 2 * Real.exp (Tmax * (mtop : ℝ)) ≤ (1 / 2 : ℝ) * ((S.ρ 1 : ℝ) * Real.exp Tmax) := by
    have hratio : Real.exp (Tmax * (mtop : ℝ) - Tmax) = Real.exp (- (d * Tmax)) := by
      congr 1
      dsimp [d]
      ring
    have hexp_neg : Real.exp (- (d * Tmax)) ≤ (S.ρ 1 : ℝ) / 4 := by
      have h1 : -(d * Tmax) ≤ - (Real.log (4 / (S.ρ 1 : ℝ)) + 1) := by linarith
      have h2 : - (Real.log (4 / (S.ρ 1 : ℝ)) + 1) ≤ Real.log ((S.ρ 1 : ℝ) / 4) := by
        rw [neg_add, ← Real.log_inv]
        have hinv : (4 / (S.ρ 1 : ℝ))⁻¹ = (S.ρ 1 : ℝ) / 4 := by field_simp
        rw [hinv]
        linarith
      calc Real.exp (- (d * Tmax)) ≤ Real.exp (Real.log ((S.ρ 1 : ℝ) / 4)) := Real.exp_le_exp.mpr (le_trans h1 h2)
        _ = (S.ρ 1 : ℝ) / 4 := Real.exp_log (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hexp_neg (mul_pos two_pos (Real.exp_pos Tmax)).le
    have hL : 2 * Real.exp Tmax * Real.exp (-(d * Tmax)) = 2 * Real.exp (Tmax * (mtop : ℝ)) := by
      rw [← hratio, mul_assoc, ← Real.exp_add]
      ring_nf
    rw [hL] at hmul
    linarith
  have hdiv_le : 1 - deriv (phi S) Tmax ≤ 1 / 2 := by
    rw [hdiff, div_le_iff₀ (mgf_pos S Tmax)]
    calc ∑ x ∈ S.A, (S.ρ x : ℝ) * (1 - (x : ℝ)) * Real.exp (Tmax * (x : ℝ))
        ≤ 2 * Real.exp (Tmax * (mtop : ℝ)) := hnum_le
      _ ≤ (1 / 2 : ℝ) * ((S.ρ 1 : ℝ) * Real.exp Tmax) := hexp_bound
      _ ≤ (1 / 2 : ℝ) * mgf S Tmax := by linarith [hden_ge]
  linarith

private lemma rateI_attained_mid (S : SpinLaw) (Tmax : ℝ) (hTpos : 0 < Tmax)
    (hTval : (1 / 2 : ℝ) ≤ deriv (phi S) Tmax) {m : ℝ} (hm_lo : -1 / 2 ≤ m) (hm_hi : m ≤ 1 / 2) :
    ∃ t : ℝ, -Tmax ≤ t ∧ t ≤ Tmax ∧ rateI S m = t * m - phi S t := by
  let g : ℝ → ℝ := fun t => t * m - phi S t
  have hg_cont : Continuous g := (continuous_id.mul continuous_const).sub (phi_contDiff S).continuous
  have hne : (Set.Icc (-Tmax) Tmax).Nonempty := ⟨0, by linarith, hTpos.le⟩
  obtain ⟨t₀, ht₀_mem, ht₀_max⟩ := isCompact_Icc.exists_isMaxOn hne hg_cont.continuousOn
  have hg_deriv : ∀ t, HasDerivAt g (m - deriv (phi S) t) t :=
    fun t => (((hasDerivAt_id' t).mul_const m).sub (hasDerivAt_phi S t).differentiableAt.hasDerivAt).congr_deriv (by ring)
  have hle_left : ∀ t : ℝ, t ≤ -Tmax → g t ≤ g (-Tmax) := by
    intro t ht
    have hmono : MonotoneOn g (Set.Iic (-Tmax)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Iic (-Tmax)) hg_cont.continuousOn
        (fun s _ => (hg_deriv s).differentiableAt.differentiableWithinAt) ?_
      intro s hs
      rw [(hg_deriv s).deriv]
      have hds : deriv (phi S) s ≤ deriv (phi S) (-Tmax) :=
        deriv_phi_monotone S (@interior_subset ℝ _ (Set.Iic (-Tmax)) s hs)
      rw [deriv_phi_neg] at hds
      linarith
    exact hmono ht (Set.mem_Iic.mpr le_rfl) ht
  have hle_right : ∀ t : ℝ, Tmax ≤ t → g t ≤ g Tmax := by
    intro t ht
    have hanti : AntitoneOn g (Set.Ici Tmax) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici Tmax) hg_cont.continuousOn
        (fun s _ => (hg_deriv s).differentiableAt.differentiableWithinAt) ?_
      intro s hs
      rw [(hg_deriv s).deriv]
      have hds : deriv (phi S) Tmax ≤ deriv (phi S) s :=
        deriv_phi_monotone S (@interior_subset ℝ _ (Set.Ici Tmax) s hs)
      linarith
    exact hanti (Set.mem_Ici.mpr le_rfl) ht ht
  have hall : ∀ t : ℝ, g t ≤ g t₀ := by
    intro t
    rcases le_total t (-Tmax) with ht1 | ht1
    · exact le_trans (hle_left t ht1) (ht₀_max ⟨le_rfl, by linarith⟩)
    · rcases le_total t Tmax with ht2 | ht2
      · exact ht₀_max ⟨ht1, ht2⟩
      · exact le_trans (hle_right t ht2) (ht₀_max ⟨by linarith, le_rfl⟩)
  refine ⟨t₀, ht₀_mem.1, ht₀_mem.2, ?_⟩
  have hm_abs : |m| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb := rateI_bddAbove S hm_abs
  unfold rateI
  exact le_antisymm (ciSup_le hall) (le_ciSup hb t₀)

end SpinBasics

section SingleCloud

private def negCfg (S : SpinLaw) {r : ℕ} (τ : Config S (Fin r)) : Config S (Fin r) :=
  fun α => ⟨-(τ α : ℚ), S.neg_mem _ (τ α).2⟩

private lemma negCfg_negCfg (S : SpinLaw) {r : ℕ} (τ : Config S (Fin r)) :
    negCfg S (negCfg S τ) = τ := by
  ext α
  simp [negCfg]

private def negCfgEquiv (S : SpinLaw) (r : ℕ) : Config S (Fin r) ≃ Config S (Fin r) where
  toFun := negCfg S
  invFun := negCfg S
  left_inv := negCfg_negCfg S
  right_inv := negCfg_negCfg S

private lemma oneSum_negCfg (S : SpinLaw) {r : ℕ} (τ : Config S (Fin r)) :
    oneSum (negCfg S τ) = - oneSum τ := by
  unfold oneSum spinVal negCfg
  simp only [Rat.cast_neg, Finset.sum_neg_distrib]

private lemma prodRho_negCfg (S : SpinLaw) {r : ℕ} (τ : Config S (Fin r)) :
    prodRho S (negCfg S τ) = prodRho S τ := by
  unfold prodRho negCfg
  refine Finset.prod_congr rfl ?_
  intro α _
  simp only [S.symm _ (τ α).2]

private lemma cloudWeight_negCfg (S : SpinLaw) (β : ℝ) {r : ℕ} (τ : Config S (Fin r)) :
    cloudWeight S β (negCfg S τ) = cloudWeight S β τ := by
  unfold cloudWeight
  rw [prodRho_negCfg, oneSum_negCfg, neg_sq]

private lemma prodRho_nonneg (S : SpinLaw) {r : ℕ} (τ : Config S (Fin r)) : 0 ≤ prodRho S τ := by
  unfold prodRho
  refine Finset.prod_nonneg ?_
  intro α _
  exact_mod_cast (S.pos _ (τ α).2).le

private lemma cloudWeight_pos (S : SpinLaw) (β : ℝ) {r : ℕ} (τ : Config S (Fin r)) :
    0 < cloudWeight S β τ := by
  unfold cloudWeight prodRho
  have hprod : 0 < ∏ α : Fin r, ((S.ρ (τ α : ℚ) : ℚ) : ℝ) :=
    Finset.prod_pos fun α _ => by exact_mod_cast S.pos _ (τ α).2
  exact mul_pos hprod (Real.exp_pos _)

private lemma abs_oneSum_le (S : SpinLaw) {r : ℕ} (τ : Config S (Fin r)) :
    |oneSum τ| ≤ (r : ℝ) := by
  unfold oneSum spinVal
  calc |∑ α : Fin r, ((τ α : ℚ) : ℝ)|
      ≤ ∑ α : Fin r, |((τ α : ℚ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _α : Fin r, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro α _
        have h := S.mem_Icc (τ α : ℚ) (τ α).2
        rw [abs_le]
        constructor
        · exact_mod_cast h.1
        · exact_mod_cast h.2
    _ = (r : ℝ) := by simp

private lemma zPlus_eq_half_sum (S : SpinLaw) (β : ℝ) (r : ℕ) :
    zPlus S β r = (1 / 2 : ℝ) * ∑ τ : Config S (Fin r), cloudWeight S β τ := by
  have hswap : zPlus S β r =
      ∑ τ : Config S (Fin r), cloudWeight S β τ *
        ((if oneSum τ < 0 then (1 : ℝ) else 0) + (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0)) := by
    unfold zPlus
    refine (Fintype.sum_equiv (negCfgEquiv S r) _ _ ?_).symm
    intro τ
    dsimp only [negCfgEquiv, Equiv.coe_fn_mk]
    rw [cloudWeight_negCfg, oneSum_negCfg]
    simp [neg_pos, neg_eq_zero]
  have h2 : 2 * zPlus S β r = ∑ τ : Config S (Fin r), cloudWeight S β τ := by
    calc 2 * zPlus S β r = zPlus S β r + zPlus S β r := two_mul _
      _ = (∑ τ : Config S (Fin r), cloudWeight S β τ *
            ((if 0 < oneSum τ then (1 : ℝ) else 0) + (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0))) +
          (∑ τ : Config S (Fin r), cloudWeight S β τ *
            ((if oneSum τ < 0 then (1 : ℝ) else 0) + (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0))) := by
          congr 1
      _ = ∑ τ : Config S (Fin r), cloudWeight S β τ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro τ _
          rcases lt_trichotomy (oneSum τ) 0 with h | h | h
          · simp [h.not_gt, h, h.ne]
          · simp [h]; ring
          · simp [h, h.not_gt, h.ne']
  linarith

private lemma zPlus_pos (S : SpinLaw) (β : ℝ) (r : ℕ) : 0 < zPlus S β r := by
  rw [zPlus_eq_half_sum]
  have hne : Nonempty (Config S (Fin r)) := ⟨fun _ => ⟨1, S.one_mem⟩⟩
  have hsum : 0 < ∑ τ : Config S (Fin r), cloudWeight S β τ :=
    Finset.sum_pos (fun τ _ => cloudWeight_pos S β τ) Finset.univ_nonempty
  linarith

private lemma nuPm_nonneg (S : SpinLaw) (β : ℝ) {r : ℕ} (s : Bool) (τ : Config S (Fin r)) :
    0 ≤ nuPm S β s τ := by
  unfold nuPm
  have hw := (cloudWeight_pos S β τ).le
  have hz := (zPlus_pos S β r).le
  refine mul_nonneg (div_nonneg hw hz) ?_
  split_ifs <;> norm_num

private lemma nuPm_sum_one (S : SpinLaw) (β : ℝ) (r : ℕ) (s : Bool) :
    ∑ τ : Config S (Fin r), nuPm S β s τ = 1 := by
  have hzpos := zPlus_pos S β r
  cases s
  · have hswap : ∑ τ : Config S (Fin r), nuPm S β false τ = zPlus S β r / zPlus S β r := by
      have heq : ∑ τ : Config S (Fin r), nuPm S β false τ =
          (∑ τ : Config S (Fin r), cloudWeight S β τ *
            ((if 0 < spinOf false * oneSum τ then (1 : ℝ) else 0) +
              (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0))) / zPlus S β r := by
        unfold nuPm
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl ?_
        intro τ _
        ring
      rw [heq]
      congr 1
      refine Fintype.sum_equiv (negCfgEquiv S r) _ _ ?_
      intro τ
      dsimp only [negCfgEquiv, Equiv.coe_fn_mk]
      rw [cloudWeight_negCfg, oneSum_negCfg]
      simp [spinOf]
    rw [hswap, div_self hzpos.ne']
  · have heq : ∑ τ : Config S (Fin r), nuPm S β true τ = zPlus S β r / zPlus S β r := by
      unfold nuPm zPlus
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro τ _
      simp only [spinOf, ↓reduceIte, one_mul]
      ring
    rw [heq, div_self hzpos.ne']

private lemma nuPm_symm_expectation (S : SpinLaw) (β : ℝ) (r : ℕ) (s : Bool)
    (g : Config S (Fin r) → ℝ) (hg : ∀ τ, g (negCfg S τ) = g τ) :
    ∑ τ : Config S (Fin r), nuPm S β s τ * g τ =
      (∑ τ : Config S (Fin r), cloudWeight S β τ * g τ) /
        (∑ τ : Config S (Fin r), cloudWeight S β τ) := by
  have hz : zPlus S β r = (1 / 2 : ℝ) * ∑ τ : Config S (Fin r), cloudWeight S β τ :=
    zPlus_eq_half_sum S β r
  have hzpos := zPlus_pos S β r
  have h1 : ∀ s' : Bool,
      ∑ τ : Config S (Fin r), nuPm S β s' τ * g τ =
        (∑ τ : Config S (Fin r), cloudWeight S β τ * g τ *
          ((if 0 < oneSum τ then (1 : ℝ) else 0) + (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0))) /
          zPlus S β r := by
    intro s'
    cases s'
    · have heq : ∑ τ : Config S (Fin r), nuPm S β false τ * g τ =
          (∑ τ : Config S (Fin r), cloudWeight S β τ * g τ *
            ((if 0 < spinOf false * oneSum τ then (1 : ℝ) else 0) +
              (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0))) / zPlus S β r := by
        unfold nuPm
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun τ _ => by ring
      rw [heq]
      congr 1
      refine Fintype.sum_equiv (negCfgEquiv S r) _ _ ?_
      intro τ
      dsimp only [negCfgEquiv, Equiv.coe_fn_mk]
      rw [cloudWeight_negCfg, hg, oneSum_negCfg]
      simp only [spinOf, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, neg_pos, neg_eq_zero]
    · rw [Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro τ _
      unfold nuPm
      simp only [spinOf, ↓reduceIte, one_mul]
      ring
  rw [h1 s]
  have hswap :
      ∑ τ : Config S (Fin r), cloudWeight S β τ * g τ *
        ((if 0 < oneSum τ then (1 : ℝ) else 0) + (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0)) =
      ∑ τ : Config S (Fin r), cloudWeight S β τ * g τ *
        ((if oneSum τ < 0 then (1 : ℝ) else 0) + (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0)) := by
    refine (Fintype.sum_equiv (negCfgEquiv S r) _ _ ?_).symm
    intro τ
    dsimp only [negCfgEquiv, Equiv.coe_fn_mk]
    rw [cloudWeight_negCfg, hg, oneSum_negCfg]
    simp [neg_pos, neg_eq_zero]
  have h2 : 2 * (∑ τ : Config S (Fin r), cloudWeight S β τ * g τ *
        ((if 0 < oneSum τ then (1 : ℝ) else 0) + (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0))) =
      ∑ τ : Config S (Fin r), cloudWeight S β τ * g τ := by
    calc 2 * (∑ τ : Config S (Fin r), cloudWeight S β τ * g τ *
            ((if 0 < oneSum τ then (1 : ℝ) else 0) + (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0)))
        = (∑ τ : Config S (Fin r), cloudWeight S β τ * g τ *
            ((if 0 < oneSum τ then (1 : ℝ) else 0) + (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0))) +
          (∑ τ : Config S (Fin r), cloudWeight S β τ * g τ *
            ((if oneSum τ < 0 then (1 : ℝ) else 0) + (1 / 2 : ℝ) * (if oneSum τ = 0 then (1 : ℝ) else 0))) := by
          rw [two_mul, hswap]
      _ = ∑ τ : Config S (Fin r), cloudWeight S β τ * g τ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro τ _
          rcases lt_trichotomy (oneSum τ) 0 with h | h | h
          · simp [h.not_gt, h, h.ne]
          · simp [h]; ring
          · simp [h, h.not_gt, h.ne']
  rw [hz, ← h2]
  ring

private lemma sum_prod_tilt (S : SpinLaw) (t : ℝ) (r : ℕ) :
    (∑ τ : Config S (Fin r), ∏ α : Fin r, tilt S t (τ α : ℚ)) = 1 := by
  have h1 : (∑ τ : Config S (Fin r), ∏ α : Fin r, tilt S t (τ α : ℚ)) =
      ∏ _α : Fin r, ∑ x : {x : ℚ // x ∈ S.A}, tilt S t (x : ℚ) :=
    (Fintype.prod_sum (fun (_α : Fin r) (x : {x : ℚ // x ∈ S.A}) => tilt S t (x : ℚ))).symm
  rw [h1]
  have hsingle : ∑ x : {x : ℚ // x ∈ S.A}, tilt S t (x : ℚ) = 1 := by
    rw [Finset.sum_coe_sort S.A (fun x => tilt S t x)]
    unfold tilt
    have hpull : ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ) - phi S t) =
        ∑ x ∈ S.A, ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) * Real.exp (-phi S t) := by
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    rw [hpull, ← Finset.sum_mul]
    change mgf S t * Real.exp (-phi S t) = 1
    have hphi : phi S t = Real.log (mgf S t) := rfl
    rw [hphi, Real.exp_neg, Real.exp_log (mgf_pos S t), mul_inv_cancel₀ (mgf_pos S t).ne']
  exact Finset.prod_eq_one fun _ _ => hsingle

private lemma sum_prodRho_one (S : SpinLaw) (r : ℕ) :
    (∑ τ : Config S (Fin r), prodRho S τ) = 1 := by
  have h := sum_prod_tilt S 0 r
  convert h using 2 with τ
  unfold prodRho tilt
  refine Finset.prod_congr rfl ?_
  intro α _
  simp [phi_zero]

private lemma prod_tilt_eq (S : SpinLaw) (t : ℝ) {r : ℕ} (τ : Config S (Fin r)) :
    (∏ α : Fin r, tilt S t (τ α : ℚ)) =
      prodRho S τ * Real.exp (t * oneSum τ - (r : ℝ) * phi S t) := by
  unfold tilt prodRho oneSum spinVal
  simp_rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]

private lemma cloudWeight_eq_tilt (S : SpinLaw) (β t : ℝ) {r : ℕ} (τ : Config S (Fin r)) :
    cloudWeight S β τ =
      (∏ α : Fin r, tilt S t (τ α : ℚ)) *
        Real.exp ((r : ℝ) * phi S t - t * oneSum τ + β / (2 * (r : ℝ)) * oneSum τ ^ 2) := by
  rw [prod_tilt_eq, mul_assoc, ← Real.exp_add]
  unfold cloudWeight
  congr 2
  ring

private lemma total_cloudWeight_ge_exp (S : SpinLaw) (θ u : ℝ) (r : ℕ) (hr : 1 ≤ r) (hθ : 0 < θ)
    (hu_abs : |u| ≤ 1) (hu_fp : u = deriv (phi S) ((tau S + θ) * u)) :
    Real.exp ((r : ℝ) * Ftheta S θ u) ≤ ∑ τ : Config S (Fin r), cloudWeight S (tau S + θ) τ := by
  let β := tau S + θ
  let t₀ := β * u
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hrate : rateI S u = t₀ * u - phi S t₀ := rateI_eq_at_deriv S hu_fp hu_abs
  have hF : Ftheta S θ u = phi S t₀ - (β / 2) * u ^ 2 := by
    unfold Ftheta
    rw [hrate]
    dsimp [β, t₀]
    ring
  have hpt : ∀ τ : Config S (Fin r),
      (∏ α : Fin r, tilt S t₀ (τ α : ℚ)) * Real.exp ((r : ℝ) * Ftheta S θ u) ≤ cloudWeight S β τ := by
    intro τ
    rw [cloudWeight_eq_tilt S β t₀ τ]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun α _ => by
      unfold tilt
      have := (S.pos _ (τ α).2).le
      positivity)
    rw [Real.exp_le_exp, hF]
    have hβ : 0 ≤ β := (add_pos (tau_pos S) hθ).le
    have hsq : 0 ≤ β / (2 * (r : ℝ)) * (oneSum τ - (r : ℝ) * u) ^ 2 := by positivity
    have hid : (r : ℝ) * phi S t₀ - t₀ * oneSum τ + β / (2 * (r : ℝ)) * oneSum τ ^ 2 =
        (r : ℝ) * (phi S t₀ - β / 2 * u ^ 2) + β / (2 * (r : ℝ)) * (oneSum τ - (r : ℝ) * u) ^ 2 := by
      dsimp [t₀]
      field_simp [hrpos.ne']
      ring
    linarith
  calc Real.exp ((r : ℝ) * Ftheta S θ u)
      = (∑ τ : Config S (Fin r), ∏ α : Fin r, tilt S t₀ (τ α : ℚ)) * Real.exp ((r : ℝ) * Ftheta S θ u) := by
          rw [sum_prod_tilt, one_mul]
    _ = ∑ τ : Config S (Fin r), (∏ α : Fin r, tilt S t₀ (τ α : ℚ)) * Real.exp ((r : ℝ) * Ftheta S θ u) := by
          rw [Finset.sum_mul]
    _ ≤ ∑ τ : Config S (Fin r), cloudWeight S β τ := Finset.sum_le_sum fun τ _ => hpt τ

private lemma sum_subset_cloudWeight_le (S : SpinLaw) (β t B : ℝ) (r : ℕ)
    (E : Finset (Config S (Fin r)))
    (hE : ∀ τ ∈ E, (r : ℝ) * phi S t - t * oneSum τ + β / (2 * (r : ℝ)) * oneSum τ ^ 2 ≤ B) :
    ∑ τ ∈ E, cloudWeight S β τ ≤ Real.exp B := by
  have htilt_nn : ∀ τ : Config S (Fin r), 0 ≤ ∏ α : Fin r, tilt S t (τ α : ℚ) := fun τ =>
    Finset.prod_nonneg fun α _ => by
      unfold tilt
      have := (S.pos _ (τ α).2).le
      positivity
  calc ∑ τ ∈ E, cloudWeight S β τ
      ≤ ∑ τ ∈ E, (∏ α : Fin r, tilt S t (τ α : ℚ)) * Real.exp B := by
          refine Finset.sum_le_sum ?_
          intro τ hτ
          rw [cloudWeight_eq_tilt S β t τ]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hE τ hτ)) (htilt_nn τ)
    _ = (∑ τ ∈ E, ∏ α : Fin r, tilt S t (τ α : ℚ)) * Real.exp B := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ τ : Config S (Fin r), ∏ α : Fin r, tilt S t (τ α : ℚ)) * Real.exp B := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos B).le
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) fun τ _ _ => htilt_nn τ
    _ = Real.exp B := by rw [sum_prod_tilt, one_mul]

private lemma zero_sum_single_le (S : SpinLaw) (θ u : ℝ) (r : ℕ) (s : Bool)
    (hr : 1 ≤ r) (hθ : 0 < θ) (hu_abs : |u| ≤ 1)
    (hu_fp : u = deriv (phi S) ((tau S + θ) * u)) :
    ∑ τ : Config S (Fin r), nuPm S (tau S + θ) s τ * (if oneSum τ = 0 then (1 : ℝ) else 0) ≤
      Real.exp (-((r : ℝ) * Ftheta S θ u)) := by
  have hsymm : ∀ τ : Config S (Fin r),
      (if oneSum (negCfg S τ) = 0 then (1 : ℝ) else 0) = (if oneSum τ = 0 then (1 : ℝ) else 0) := by
    intro τ
    simp only [oneSum_negCfg, neg_eq_zero]
  rw [nuPm_symm_expectation S (tau S + θ) r s _ hsymm]
  have hnum : ∑ τ : Config S (Fin r), cloudWeight S (tau S + θ) τ * (if oneSum τ = 0 then (1 : ℝ) else 0) ≤ 1 := by
    calc ∑ τ : Config S (Fin r), cloudWeight S (tau S + θ) τ * (if oneSum τ = 0 then (1 : ℝ) else 0)
        ≤ ∑ τ : Config S (Fin r), prodRho S τ := by
            refine Finset.sum_le_sum ?_
            intro τ _
            by_cases h0 : oneSum τ = 0
            · simp [cloudWeight, h0]
            · simp [h0, prodRho_nonneg S τ]
      _ = 1 := sum_prodRho_one S r
  have hden := total_cloudWeight_ge_exp S θ u r hr hθ hu_abs hu_fp
  have hden_pos : 0 < Real.exp ((r : ℝ) * Ftheta S θ u) := Real.exp_pos _
  have hsum_pos : 0 < ∑ τ : Config S (Fin r), cloudWeight S (tau S + θ) τ := lt_of_lt_of_le hden_pos hden
  rw [div_le_iff₀ hsum_pos, Real.exp_neg]
  calc ∑ τ : Config S (Fin r), cloudWeight S (tau S + θ) τ * (if oneSum τ = 0 then (1 : ℝ) else 0)
      ≤ 1 := hnum
    _ = (Real.exp ((r : ℝ) * Ftheta S θ u))⁻¹ * Real.exp ((r : ℝ) * Ftheta S θ u) :=
        (inv_mul_cancel₀ hden_pos.ne').symm
    _ ≤ (Real.exp ((r : ℝ) * Ftheta S θ u))⁻¹ * ∑ τ : Config S (Fin r), cloudWeight S (tau S + θ) τ :=
        mul_le_mul_of_nonneg_left hden (by positivity)

private lemma sq_three_sum_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

private lemma Ftheta_le_half_θ_sq (S : SpinLaw) (hS : IsGHS S) (θ m : ℝ) (hm : |m| ≤ 1) :
    Ftheta S θ m ≤ (θ / 2) * m ^ 2 := by
  unfold Ftheta
  have hq := rateI_ge_quad S hS hm
  linarith

private lemma tail_compact_cover (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
    (θ₀_loc c_loc C_loc : ℝ) (hθ₀_pos : 0 < θ₀_loc) (_hc_pos : 0 < c_loc) (hC_pos : 0 < C_loc)
    (hprop : ∀ θ : ℝ, 0 < θ → θ ≤ θ₀_loc → ∃ u : ℝ,
      (0 < u ∧ u < 1 ∧ u = deriv (phi S) ((tau S + θ) * u)) ∧
      (∀ u' : ℝ, 0 < u' → u' < 1 → u' = deriv (phi S) ((tau S + θ) * u') → u' = u) ∧
      c_loc * θ ^ (1 / (2 * (p : ℝ) - 2)) ≤ u ∧ u ≤ C_loc * θ ^ (1 / (2 * (p : ℝ) - 2)) ∧
      c_loc * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) ≤ θ * u ^ 2 ∧
      θ * u ^ 2 ≤ C_loc * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) ∧
      Ftheta S θ (-u) = Ftheta S θ u ∧
      (∀ m : ℝ, |m| ≤ 1 → Ftheta S θ m ≤ Ftheta S θ u) ∧
      (∀ m : ℝ, |m| ≤ 1 → c_loc * θ * (|m| - u) ^ 2 ≤ Ftheta S θ u - Ftheta S θ m)) :
    ∃ (θ₁ : ℝ) (s_cov : Finset (ℝ × ℝ)),
      0 < θ₁ ∧ θ₁ ≤ θ₀_loc ∧
      ∀ m : ℝ, 1 / 2 ≤ m → m ≤ 1 →
        ∃ tk ∈ s_cov, (tau S / 2) * m ^ 2 + θ₁ / 32 ≤ tk.1 * m - phi S tk.1 := by
  have hp2 : 2 ≤ p := hp.1
  have hpR1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  let a : ℝ := min (1 / 2) (1 / (8 * (C_loc + 1)))
  have ha_pos : 0 < a := lt_min (by norm_num) (by positivity)
  have ha_le1 : a ≤ 1 / (8 * (C_loc + 1)) := min_le_right _ _
  let θ₁ : ℝ := min θ₀_loc (a ^ (p - 1))
  have hθ₁_pos : 0 < θ₁ := lt_min hθ₀_pos (pow_pos ha_pos _)
  have hθ₁_le_loc : θ₁ ≤ θ₀_loc := min_le_left _ _
  have hθ₁_le_pow : θ₁ ≤ a ^ (p - 1) := min_le_right _ _
  obtain ⟨u₁, hu₁_fp, _, _, _, _, hθu₁_ub, _, hmax₁, _⟩ := hprop θ₁ hθ₁_pos hθ₁_le_loc
  have hpow_le : θ₁ ^ ((p : ℝ) / ((p : ℝ) - 1)) ≤ a * θ₁ := by
    have hsplit : (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by
      field_simp [hpR1.ne']
      ring
    rw [hsplit, Real.rpow_add hθ₁_pos, Real.rpow_one]
    have hr1 : θ₁ ^ (1 / ((p : ℝ) - 1)) ≤ a := by
      have hcast : a ^ (p - 1) = a ^ ((p : ℝ) - 1) := by
        rw [← Real.rpow_natCast a (p - 1)]
        congr 1
        have hp1 : 1 ≤ p := by omega
        push_cast [hp1]
        rfl
      calc θ₁ ^ (1 / ((p : ℝ) - 1))
          ≤ (a ^ ((p : ℝ) - 1)) ^ (1 / ((p : ℝ) - 1)) :=
              Real.rpow_le_rpow hθ₁_pos.le (by rw [← hcast]; exact hθ₁_le_pow) (by positivity)
        _ = a ^ (((p : ℝ) - 1) * (1 / ((p : ℝ) - 1))) := (Real.rpow_mul ha_pos.le _ _).symm
        _ = a ^ (1 : ℝ) := by congr 1; field_simp [hpR1.ne']
        _ = a := Real.rpow_one a
    calc θ₁ * θ₁ ^ (1 / ((p : ℝ) - 1)) ≤ θ₁ * a := mul_le_mul_of_nonneg_left hr1 hθ₁_pos.le
      _ = a * θ₁ := mul_comm _ _
  have hFu₁_le : Ftheta S θ₁ u₁ ≤ θ₁ / 16 := by
    have hu₁_abs : |u₁| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu₁_fp.1, hu₁_fp.2.1]
    have h1 := Ftheta_le_half_θ_sq S hS θ₁ u₁ hu₁_abs
    have h2 : θ₁ * u₁ ^ 2 ≤ a * C_loc * θ₁ := by
      calc θ₁ * u₁ ^ 2 ≤ C_loc * θ₁ ^ ((p : ℝ) / ((p : ℝ) - 1)) := hθu₁_ub
        _ ≤ C_loc * (a * θ₁) := mul_le_mul_of_nonneg_left hpow_le hC_pos.le
        _ = a * C_loc * θ₁ := by ring
    have h3 : a * C_loc ≤ 1 / 8 := by
      calc a * C_loc ≤ (1 / (8 * (C_loc + 1))) * C_loc := mul_le_mul_of_nonneg_right ha_le1 hC_pos.le
        _ ≤ 1 / 8 := by
            rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
    calc Ftheta S θ₁ u₁ ≤ (1 / 2) * (θ₁ * u₁ ^ 2) := by linarith
      _ ≤ (1 / 2) * (a * C_loc * θ₁) := by linarith
      _ ≤ (1 / 2) * ((1 / 8) * θ₁) := by
          have : a * C_loc * θ₁ ≤ (1 / 8) * θ₁ := mul_le_mul_of_nonneg_right h3 hθ₁_pos.le
          linarith
      _ = θ₁ / 16 := by ring
  have hrate_gt : ∀ m : ℝ, 1 / 2 ≤ m → m ≤ 1 →
      (tau S / 2) * m ^ 2 + θ₁ / 32 < rateI S m := by
    intro m hm_lo hm_hi
    have hm_abs : |m| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have hm_sq : (1 / 4 : ℝ) ≤ m ^ 2 := by nlinarith only [hm_lo]
    have hFm := hmax₁ m hm_abs
    have hdiff : (tau S / 2) * m ^ 2 - rateI S m = Ftheta S θ₁ m - (θ₁ / 2) * m ^ 2 := by
      unfold Ftheta; ring
    have hle : (tau S / 2) * m ^ 2 - rateI S m ≤ - (θ₁ / 16) := by
      have : (θ₁ / 2) * (1 / 4) ≤ (θ₁ / 2) * m ^ 2 := mul_le_mul_of_nonneg_left hm_sq (by positivity)
      linarith
    linarith
  have hopen : ∀ m ∈ Set.Icc (1 / 2 : ℝ) 1, ∃ t : ℝ, ∃ δ : ℝ, 0 < δ ∧
      ∀ m' ∈ Metric.ball m δ, (tau S / 2) * m' ^ 2 + θ₁ / 32 ≤ t * m' - phi S t := by
    intro m hm
    have hgt := hrate_gt m hm.1 hm.2
    have hne : (Set.range (fun t : ℝ => t * m - phi S t)).Nonempty := ⟨0 * m - phi S 0, 0, rfl⟩
    have hm_abs : |m| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hm.1, hm.2]
    obtain ⟨t, ht⟩ := (lt_ciSup_iff (rateI_bddAbove S hm_abs)).mp hgt
    let f : ℝ → ℝ := fun m' => (t * m' - phi S t) - ((tau S / 2) * m' ^ 2 + θ₁ / 32)
    have hf_cont : Continuous f :=
      ((continuous_const.mul continuous_id).sub continuous_const).sub
        ((continuous_const.mul (continuous_pow 2)).add continuous_const)
    have hfm : 0 < f m := sub_pos.mpr ht
    have hnhds : ∀ᶠ m' in nhds m, 0 < f m' := hf_cont.continuousAt.eventually (lt_mem_nhds hfm)
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hnhds
    refine ⟨t, δ, hδ_pos, fun m' hm' => ?_⟩
    have := hδ m' hm'
    dsimp [f] at this
    linarith
  choose t_fn δ_fn hδ_pos_fn hδ_prop_fn using fun m : Set.Icc (1 / 2 : ℝ) 1 => hopen m.1 m.2
  have hcov_ball : Set.Icc (1 / 2 : ℝ) 1 ⊆ ⋃ m : Set.Icc (1 / 2 : ℝ) 1, Metric.ball (m : ℝ) (δ_fn m) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hδ_pos_fn ⟨x, hx⟩)⟩
  obtain ⟨s_sub, hs_sub⟩ := isCompact_Icc.elim_finite_subcover
    (fun m : Set.Icc (1 / 2 : ℝ) 1 => Metric.ball (m : ℝ) (δ_fn m))
    (fun _ => Metric.isOpen_ball) hcov_ball
  refine ⟨θ₁, s_sub.image (fun m => (t_fn m, 0)), hθ₁_pos, hθ₁_le_loc, ?_⟩
  intro m hm_lo hm_hi
  obtain ⟨k, hk_mem, hk_ball⟩ := Set.mem_iUnion₂.mp (hs_sub ⟨hm_lo, hm_hi⟩)
  refine ⟨(t_fn k, 0), Finset.mem_image_of_mem _ hk_mem, ?_⟩
  exact hδ_prop_fn k m hk_ball

private lemma exp_moment_single_cloud (S : SpinLaw) (p : ℕ) (hS : IsGHS S)
    (Tmax : ℝ) (hTmax_pos : 0 < Tmax) (hTmax_val : (1 / 2 : ℝ) ≤ deriv (phi S) Tmax)
    (θ₁ c_loc : ℝ) (hθ₁_pos : 0 < θ₁) (hc_loc_pos : 0 < c_loc)
    (s_cov : Finset (ℝ × ℝ))
    (hcov : ∀ m : ℝ, 1 / 2 ≤ m → m ≤ 1 →
      ∃ tk ∈ s_cov, (tau S / 2) * m ^ 2 + θ₁ / 32 ≤ tk.1 * m - phi S tk.1) :
    ∃ θ₀_cap : ℝ, ∃ Kpow : ℕ, 0 < θ₀_cap ∧ θ₀_cap ≤ θ₁ ∧
      ∀ (r : ℕ) (θ u û Λ : ℝ) (s : Bool),
        1 ≤ r →
        ((2 * (s_cov.card : ℝ) + 1) * (128 / θ₁)) ≤ (r : ℝ) →
        0 < θ → θ ≤ θ₀_cap →
        0 < u → u < 1 → u = deriv (phi S) ((tau S + θ) * u) →
        (∀ m : ℝ, |m| ≤ 1 → c_loc * θ * (|m| - u) ^ 2 ≤ Ftheta S θ u - Ftheta S θ m) →
        |û - u| ≤ 1 / (r : ℝ) ^ 3 → u / 2 ≤ û → û ≤ 2 * u →
        0 ≤ Λ → Λ ≤ (c_loc / 3) * (r : ℝ) * θ * û ^ 2 →
        ∑ τ : Config S (Fin r), nuPm S (tau S + θ) s τ *
            Real.exp (Λ * (|oneSum τ| / ((r : ℝ) * û) - 1) ^ 2) ≤
          ((r : ℝ) + 1) ^ Kpow := by
  let Cmid : ℝ := Tmax + tau S + θ₁ + 1
  have hCmid_pos : 0 < Cmid := by dsimp [Cmid]; linarith [tau_pos S, hTmax_pos, hθ₁_pos]
  let Kpow : ℕ := Nat.ceil ((Cmid + 2) * Real.exp 3 + 1) + 1
  let θ₀_cap : ℝ := min θ₁ (min (1 / (c_loc + 1)) (θ₁ / (256 * (12 * c_loc + 1))))
  refine ⟨θ₀_cap, Kpow, lt_min hθ₁_pos (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_⟩
  intro r θ u û Λ s hr hr_big hθ_pos hθ_le hu_pos hu_lt1 hu_fp hF_gap hû_diff hû_lo hû_hi hΛ_nn hΛ_le
  have hθ_le_θ₁ : θ ≤ θ₁ := le_trans hθ_le (min_le_left _ _)
  have hθ_le_c : θ ≤ 1 / (c_loc + 1) := le_trans hθ_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hθ_le_tail : θ ≤ θ₁ / (256 * (12 * c_loc + 1)) :=
    le_trans hθ_le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hu_abs : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hû_pos : 0 < û := lt_of_lt_of_le (by positivity) hû_lo
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  let β : ℝ := tau S + θ
  let δfn : Config S (Fin r) → ℝ := fun τ => |oneSum τ| / ((r : ℝ) * û) - 1
  have hsymm : ∀ τ : Config S (Fin r),
      Real.exp (Λ * δfn (negCfg S τ) ^ 2) = Real.exp (Λ * δfn τ ^ 2) := by
    intro τ
    dsimp [δfn]
    rw [oneSum_negCfg, abs_neg]
  rw [nuPm_symm_expectation S β r s _ hsymm]
  have hZ_ge := total_cloudWeight_ge_exp S θ u r hr hθ_pos hu_abs hu_fp
  have hZ_pos : 0 < ∑ τ : Config S (Fin r), cloudWeight S β τ :=
    lt_of_lt_of_le (Real.exp_pos _) hZ_ge
  let E_mid : Finset (Config S (Fin r)) :=
    Finset.univ.filter (fun τ => |oneSum τ / (r : ℝ)| ≤ 1 / 2)
  let E_hi : Finset (Config S (Fin r)) :=
    Finset.univ.filter (fun τ => 1 / 2 < oneSum τ / (r : ℝ))
  let E_lo : Finset (Config S (Fin r)) :=
    Finset.univ.filter (fun τ => oneSum τ / (r : ℝ) < -1 / 2)
  have hsplit_sum :
      ∑ τ : Config S (Fin r), cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) ≤
        (∑ τ ∈ E_mid, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) +
        (∑ τ ∈ E_hi, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) +
        (∑ τ ∈ E_lo, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) := by
    have hpt : ∀ τ : Config S (Fin r),
        cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) ≤
          (if τ ∈ E_mid then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) +
          (if τ ∈ E_hi then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) +
          (if τ ∈ E_lo then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) := by
      intro τ
      have hterm_nn : 0 ≤ cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) :=
        mul_nonneg (cloudWeight_pos S β τ).le (Real.exp_pos _).le
      rcases lt_or_ge (|oneSum τ / (r : ℝ)|) (1 / 2) with h | h
      · have hm : τ ∈ E_mid := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.le⟩
        simp only [hm, ↓reduceIte]
        have : 0 ≤ (if τ ∈ E_hi then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) := by
          split_ifs <;> [exact hterm_nn; exact le_rfl]
        have : 0 ≤ (if τ ∈ E_lo then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) := by
          split_ifs <;> [exact hterm_nn; exact le_rfl]
        linarith
      · rcases eq_or_lt_of_le h with heq | hlt
        · have hm : τ ∈ E_mid := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.symm.le⟩
          simp only [hm, ↓reduceIte]
          have : 0 ≤ (if τ ∈ E_hi then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) := by
            split_ifs <;> [exact hterm_nn; exact le_rfl]
          have : 0 ≤ (if τ ∈ E_lo then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) := by
            split_ifs <;> [exact hterm_nn; exact le_rfl]
          linarith
        · rcases lt_abs.mp hlt with h1 | h1
          · have hh : τ ∈ E_hi := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
            simp only [hh, ↓reduceIte]
            have : 0 ≤ (if τ ∈ E_mid then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) := by
              split_ifs <;> [exact hterm_nn; exact le_rfl]
            have : 0 ≤ (if τ ∈ E_lo then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) := by
              split_ifs <;> [exact hterm_nn; exact le_rfl]
            linarith
          · have hl : τ ∈ E_lo := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩
            simp only [hl, ↓reduceIte]
            have : 0 ≤ (if τ ∈ E_mid then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) := by
              split_ifs <;> [exact hterm_nn; exact le_rfl]
            have : 0 ≤ (if τ ∈ E_hi then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) := by
              split_ifs <;> [exact hterm_nn; exact le_rfl]
            linarith
    calc ∑ τ : Config S (Fin r), cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)
        ≤ ∑ τ : Config S (Fin r),
            ((if τ ∈ E_mid then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) +
             (if τ ∈ E_hi then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) +
             (if τ ∈ E_lo then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0)) :=
            Finset.sum_le_sum fun τ _ => hpt τ
      _ = (∑ τ ∈ E_mid, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) +
          (∑ τ ∈ E_hi, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) +
          (∑ τ ∈ E_lo, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) := by
            simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
  have hE_lo_eq :
      ∑ τ ∈ E_lo, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) =
      ∑ τ ∈ E_hi, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) := by
    refine Finset.sum_bij (fun τ _ => negCfg S τ) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [E_lo, E_hi, Finset.mem_filter, Finset.mem_univ, true_and, oneSum_negCfg, neg_div] at hτ ⊢
      linarith
    · intro τ₁ _ τ₂ _ h
      have := congrArg (negCfg S) h
      simpa [negCfg_negCfg] using this
    · intro τ hτ
      refine ⟨negCfg S τ, ?_, negCfg_negCfg S τ⟩
      simp only [E_lo, E_hi, Finset.mem_filter, Finset.mem_univ, true_and, oneSum_negCfg, neg_div] at hτ ⊢
      linarith
    · intro τ _
      rw [cloudWeight_negCfg]
      have hd : δfn (negCfg S τ) = δfn τ := by dsimp [δfn]; rw [oneSum_negCfg, abs_neg]
      rw [hd]
  have hE_hi_bound :
      (∑ τ ∈ E_hi, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) ≤
        (s_cov.card : ℝ) * Real.exp (-((r : ℝ) * θ₁ / 128)) := by
    have hδ_hi : ∀ τ ∈ E_hi, Λ * δfn τ ^ 2 ≤ (r : ℝ) * θ₁ / 256 := by
      intro τ _
      have hm_le1 : |oneSum τ| / (r : ℝ) ≤ 1 := (div_le_one hrpos).mpr (abs_oneSum_le S τ)
      have hδ_le : |δfn τ| ≤ 3 / u := by
        dsimp [δfn]
        have h1 : |(|oneSum τ| / ((r : ℝ) * û) - 1)| ≤ |oneSum τ| / ((r : ℝ) * û) + 1 :=
          abs_sub_le_iff.mpr ⟨by linarith [div_nonneg (abs_nonneg (oneSum τ)) (by positivity : 0 ≤ (r : ℝ) * û)],
            by linarith [div_nonneg (abs_nonneg (oneSum τ)) (by positivity : 0 ≤ (r : ℝ) * û)]⟩
        have h2 : |oneSum τ| / ((r : ℝ) * û) ≤ 2 / u := by
          have hdiv : |oneSum τ| / ((r : ℝ) * û) = (|oneSum τ| / (r : ℝ)) / û := by ring
          rw [hdiv]
          calc (|oneSum τ| / (r : ℝ)) / û ≤ 1 / û := div_le_div_of_nonneg_right hm_le1 hû_pos.le
            _ ≤ 1 / (u / 2) := div_le_div_of_nonneg_left zero_le_one (by positivity) hû_lo
            _ = 2 / u := by ring
        have h3 : (1 : ℝ) ≤ 1 / u := (one_le_div hu_pos).mpr hu_lt1.le
        have h23 : 2 / u + 1 / u = 3 / u := by ring
        linarith
      have hδ_sq : δfn τ ^ 2 ≤ 9 / u ^ 2 := by
        calc δfn τ ^ 2 = |δfn τ| ^ 2 := (sq_abs _).symm
          _ ≤ (3 / u) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδ_le 2
          _ = 9 / u ^ 2 := by ring
      have hθ_bnd : 12 * c_loc * θ ≤ θ₁ / 256 := by
        have hmul : θ * (256 * (12 * c_loc + 1)) ≤ θ₁ :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < 256 * (12 * c_loc + 1))).mp hθ_le_tail
        nlinarith only [hmul, hθ_pos]
      calc Λ * δfn τ ^ 2 ≤ Λ * (9 / u ^ 2) := mul_le_mul_of_nonneg_left hδ_sq hΛ_nn
        _ ≤ ((c_loc / 3) * (r : ℝ) * θ * û ^ 2) * (9 / u ^ 2) :=
            mul_le_mul_of_nonneg_right hΛ_le (by positivity)
        _ ≤ ((c_loc / 3) * (r : ℝ) * θ * (2 * u) ^ 2) * (9 / u ^ 2) := by
            have hû_sq : û ^ 2 ≤ (2 * u) ^ 2 := pow_le_pow_left₀ hû_pos.le hû_hi 2
            gcongr
        _ = (r : ℝ) * (12 * c_loc * θ) := by field_simp [hu_pos.ne']; ring
        _ ≤ (r : ℝ) * (θ₁ / 256) := mul_le_mul_of_nonneg_left hθ_bnd hrpos.le
        _ = (r : ℝ) * θ₁ / 256 := by ring
    have hθ_half_le : θ / 2 ≤ θ₁ / 256 := by
      have hmul : θ * (256 * (12 * c_loc + 1)) ≤ θ₁ :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < 256 * (12 * c_loc + 1))).mp hθ_le_tail
      nlinarith only [hmul, hc_loc_pos, hθ_pos]
    calc ∑ τ ∈ E_hi, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)
        ≤ ∑ τ ∈ E_hi, cloudWeight S β τ * Real.exp ((r : ℝ) * θ₁ / 256) := by
            refine Finset.sum_le_sum fun τ hτ =>
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hδ_hi τ hτ)) (cloudWeight_pos S β τ).le
      _ ≤ ∑ τ ∈ E_hi, ∑ tk ∈ s_cov,
            (if (tau S / 2) * (oneSum τ / (r : ℝ)) ^ 2 + θ₁ / 32 ≤
                tk.1 * (oneSum τ / (r : ℝ)) - phi S tk.1
             then cloudWeight S β τ * Real.exp ((r : ℝ) * θ₁ / 256) else 0) := by
            refine Finset.sum_le_sum fun τ hτ => ?_
            have hm_lo : 1 / 2 ≤ oneSum τ / (r : ℝ) :=
              (Finset.mem_filter.mp hτ).2.le
            have hm_hi : oneSum τ / (r : ℝ) ≤ 1 := by
              rw [div_le_one hrpos]
              exact le_trans (le_abs_self _) (abs_oneSum_le S τ)
            obtain ⟨tk₀, htk₀_mem, htk₀⟩ := hcov (oneSum τ / (r : ℝ)) hm_lo hm_hi
            have h1 : (1 : ℝ) ≤ ∑ tk ∈ s_cov,
                (if (tau S / 2) * (oneSum τ / (r : ℝ)) ^ 2 + θ₁ / 32 ≤
                    tk.1 * (oneSum τ / (r : ℝ)) - phi S tk.1
                 then (1 : ℝ) else 0) := by
              calc (1 : ℝ) = (if (tau S / 2) * (oneSum τ / (r : ℝ)) ^ 2 + θ₁ / 32 ≤
                      tk₀.1 * (oneSum τ / (r : ℝ)) - phi S tk₀.1
                   then (1 : ℝ) else 0) := by simp [htk₀]
                _ ≤ _ := Finset.single_le_sum
                    (f := fun tk => if (tau S / 2) * (oneSum τ / (r : ℝ)) ^ 2 + θ₁ / 32 ≤
                        tk.1 * (oneSum τ / (r : ℝ)) - phi S tk.1 then (1 : ℝ) else 0)
                    (fun tk _ => by split_ifs <;> norm_num) htk₀_mem
            calc cloudWeight S β τ * Real.exp ((r : ℝ) * θ₁ / 256)
                ≤ (∑ tk ∈ s_cov,
                    (if (tau S / 2) * (oneSum τ / (r : ℝ)) ^ 2 + θ₁ / 32 ≤
                        tk.1 * (oneSum τ / (r : ℝ)) - phi S tk.1
                     then (1 : ℝ) else 0)) *
                    (cloudWeight S β τ * Real.exp ((r : ℝ) * θ₁ / 256)) :=
                  le_mul_of_one_le_left
                    (mul_nonneg (cloudWeight_pos S β τ).le (Real.exp_pos _).le) h1
              _ = _ := by
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun tk _ => ?_
                  split_ifs <;> ring
      _ = ∑ tk ∈ s_cov, (∑ τ ∈ E_hi.filter (fun τ =>
            (tau S / 2) * (oneSum τ / (r : ℝ)) ^ 2 + θ₁ / 32 ≤
              tk.1 * (oneSum τ / (r : ℝ)) - phi S tk.1),
            cloudWeight S β τ) * Real.exp ((r : ℝ) * θ₁ / 256) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun tk _ => ?_
            rw [Finset.sum_mul]
            conv_rhs => rw [Finset.sum_filter]
      _ ≤ ∑ _tk ∈ s_cov, Real.exp (-((r : ℝ) * θ₁ / 64)) * Real.exp ((r : ℝ) * θ₁ / 256) := by
            refine Finset.sum_le_sum fun tk _ => ?_
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            refine sum_subset_cloudWeight_le S β tk.1 (-((r : ℝ) * θ₁ / 64)) r _ ?_
            intro τ hτ
            have hcond := (Finset.mem_filter.mp hτ).2
            have hm_abs : |oneSum τ / (r : ℝ)| ≤ 1 := by
              rw [abs_div, abs_of_pos hrpos, div_le_one hrpos]
              exact abs_oneSum_le S τ
            have hm_sq : (oneSum τ / (r : ℝ)) ^ 2 ≤ 1 := by
              calc (oneSum τ / (r : ℝ)) ^ 2 = |oneSum τ / (r : ℝ)| ^ 2 := (sq_abs _).symm
                _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hm_abs 2
                _ = 1 := one_pow 2
            have hid : (r : ℝ) * phi S tk.1 - tk.1 * oneSum τ + β / (2 * (r : ℝ)) * oneSum τ ^ 2 =
                (r : ℝ) * ((tau S / 2) * (oneSum τ / (r : ℝ)) ^ 2 -
                  (tk.1 * (oneSum τ / (r : ℝ)) - phi S tk.1) +
                  (θ / 2) * (oneSum τ / (r : ℝ)) ^ 2) := by
              dsimp [β]
              field_simp [hrpos.ne']
              ring
            rw [hid]
            have hstep : (tau S / 2) * (oneSum τ / (r : ℝ)) ^ 2 -
                (tk.1 * (oneSum τ / (r : ℝ)) - phi S tk.1) + (θ / 2) * (oneSum τ / (r : ℝ)) ^ 2 ≤
                -(θ₁ / 64) := by
              have hθm : (θ / 2) * (oneSum τ / (r : ℝ)) ^ 2 ≤ θ / 2 :=
                mul_le_of_le_one_right (by positivity) hm_sq
              linarith
            calc (r : ℝ) * ((tau S / 2) * (oneSum τ / (r : ℝ)) ^ 2 -
                    (tk.1 * (oneSum τ / (r : ℝ)) - phi S tk.1) + (θ / 2) * (oneSum τ / (r : ℝ)) ^ 2)
                ≤ (r : ℝ) * (-(θ₁ / 64)) := mul_le_mul_of_nonneg_left hstep hrpos.le
              _ = -((r : ℝ) * θ₁ / 64) := by ring
      _ ≤ (s_cov.card : ℝ) * Real.exp (-((r : ℝ) * θ₁ / 128)) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← Real.exp_add]
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
            have : (0 : ℝ) ≤ (r : ℝ) * θ₁ := by positivity
            linarith
  let K : ℕ := Nat.ceil ((r : ℝ) * Cmid)
  have hK_pos : 1 ≤ K := Nat.ceil_pos.mpr (mul_pos hrpos hCmid_pos)
  have hKR_ge : (r : ℝ) * Cmid ≤ (K : ℝ) := Nat.le_ceil _
  have hK_lt : (K : ℝ) < (r : ℝ) * Cmid + 1 := Nat.ceil_lt_add_one (mul_pos hrpos hCmid_pos).le
  let η : ℝ := 1 / (K : ℝ)
  have hη_pos : 0 < η := by positivity
  have hη_le : η ≤ 1 / ((r : ℝ) * Cmid) :=
    div_le_div_of_nonneg_left zero_le_one (mul_pos hrpos hCmid_pos) hKR_ge
  let mGrid : Fin (K + 1) → ℝ := fun j => -1 / 2 + (j : ℝ) / (K : ℝ)
  have hmGrid_abs : ∀ j : Fin (K + 1), -1 / 2 ≤ mGrid j ∧ mGrid j ≤ 1 / 2 := by
    intro j
    dsimp [mGrid]
    have hj_le : (j : ℝ) ≤ (K : ℝ) := by
      have : (j : ℕ) ≤ K := Nat.lt_succ_iff.mp j.2
      exact_mod_cast this
    constructor
    · have : 0 ≤ (j : ℝ) / (K : ℝ) := by positivity
      linarith
    · have : (j : ℝ) / (K : ℝ) ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < K)).mpr hj_le
      linarith
  have hmGrid_cover : ∀ m : ℝ, |m| ≤ 1 / 2 → ∃ j : Fin (K + 1), |m - mGrid j| ≤ η := by
    intro m hm
    have hm_lo : -(1 / 2 : ℝ) ≤ m := (abs_le.mp hm).1
    have hm_hi : m ≤ 1 / 2 := (abs_le.mp hm).2
    let jNat : ℕ := Nat.floor ((K : ℝ) * (m + 1 / 2))
    have hjNat_nn : 0 ≤ (K : ℝ) * (m + 1 / 2) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have hjNat_le : jNat ≤ K := Nat.floor_le_of_le (by
      have hle : m + 1 / 2 ≤ 1 := by linarith
      nlinarith only [hle, Nat.cast_nonneg (α := ℝ) K])
    have hjNat_lt : jNat < K + 1 := Nat.lt_succ_of_le hjNat_le
    refine ⟨⟨jNat, hjNat_lt⟩, ?_⟩
    have hfl1 : (jNat : ℝ) ≤ (K : ℝ) * (m + 1 / 2) := Nat.floor_le hjNat_nn
    have hfl2 : (K : ℝ) * (m + 1 / 2) < (jNat : ℝ) + 1 := Nat.lt_floor_add_one _
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK_pos
    have hlo : 0 ≤ m - mGrid ⟨jNat, hjNat_lt⟩ := by
      dsimp [mGrid]
      have hdiv : (jNat : ℝ) / (K : ℝ) ≤ m + 1 / 2 := (div_le_iff₀ hKpos).mpr (by linarith)
      linarith
    have hhi : m - mGrid ⟨jNat, hjNat_lt⟩ ≤ η := by
      dsimp [mGrid, η]
      have hdiv : m + 1 / 2 ≤ ((jNat : ℝ) + 1) / (K : ℝ) := (le_div_iff₀ hKpos).mpr (by linarith)
      linarith [show ((jNat : ℝ) + 1) / (K : ℝ) = (jNat : ℝ) / (K : ℝ) + 1 / (K : ℝ) by ring]
    rw [abs_of_nonneg hlo]
    exact hhi
  have hE_mid_bound :
      (∑ τ ∈ E_mid, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) ≤
        ((K : ℝ) + 1) * Real.exp 3 * Real.exp ((r : ℝ) * Ftheta S θ u) := by
    calc ∑ τ ∈ E_mid, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)
        ≤ ∑ τ ∈ E_mid, ∑ j : Fin (K + 1),
            (if |oneSum τ / (r : ℝ) - mGrid j| ≤ η
             then cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) else 0) := by
            refine Finset.sum_le_sum fun τ hτ => ?_
            have hm_abs := (Finset.mem_filter.mp hτ).2
            obtain ⟨j₀, hj₀⟩ := hmGrid_cover (oneSum τ / (r : ℝ)) hm_abs
            have h1 : (1 : ℝ) ≤ ∑ j : Fin (K + 1),
                (if |oneSum τ / (r : ℝ) - mGrid j| ≤ η then (1 : ℝ) else 0) := by
              calc (1 : ℝ) = (if |oneSum τ / (r : ℝ) - mGrid j₀| ≤ η then (1 : ℝ) else 0) := by
                    simp [hj₀]
                _ ≤ _ := Finset.single_le_sum
                    (f := fun j : Fin (K + 1) =>
                      if |oneSum τ / (r : ℝ) - mGrid j| ≤ η then (1 : ℝ) else 0)
                    (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ j₀)
            calc cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)
                ≤ (∑ j : Fin (K + 1),
                    (if |oneSum τ / (r : ℝ) - mGrid j| ≤ η then (1 : ℝ) else 0)) *
                    (cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) :=
                  le_mul_of_one_le_left
                    (mul_nonneg (cloudWeight_pos S β τ).le (Real.exp_pos _).le) h1
              _ = _ := by
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  split_ifs <;> ring
      _ = ∑ j : Fin (K + 1), ∑ τ ∈ E_mid.filter (fun τ => |oneSum τ / (r : ℝ) - mGrid j| ≤ η),
            cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => by
              conv_rhs => rw [Finset.sum_filter]
      _ ≤ ∑ _j : Fin (K + 1), Real.exp ((r : ℝ) * Ftheta S θ u + 3) := by
            refine Finset.sum_le_sum fun j _ => ?_
            obtain ⟨tj, htj_lo, htj_hi, htj_rate⟩ :=
              rateI_attained_mid S Tmax hTmax_pos hTmax_val (hmGrid_abs j).1 (hmGrid_abs j).2
            let Ej := E_mid.filter (fun τ => |oneSum τ / (r : ℝ) - mGrid j| ≤ η)
            have hFmj : c_loc * θ * (|mGrid j| - u) ^ 2 ≤ Ftheta S θ u - Ftheta S θ (mGrid j) :=
              hF_gap (mGrid j) (by rw [abs_le]; constructor <;> linarith [(hmGrid_abs j).1, (hmGrid_abs j).2])
            have hδ_exp : ∀ τ ∈ Ej,
                Λ * δfn τ ^ 2 ≤ (r : ℝ) * (Ftheta S θ u - Ftheta S θ (mGrid j)) + 2 := by
              intro τ hτ
              have hbin := (Finset.mem_filter.mp hτ).2
              have htri : |δfn τ| ≤ (η + abs (|mGrid j| - u) + 1 / (r : ℝ) ^ 3) / û := by
                dsimp [δfn]
                have hnum : abs (|oneSum τ| / (r : ℝ) - û) ≤ η + abs (|mGrid j| - u) + 1 / (r : ℝ) ^ 3 := by
                  have h1 : abs (|oneSum τ| / (r : ℝ) - |mGrid j|) ≤ |oneSum τ / (r : ℝ) - mGrid j| := by
                    rw [show |oneSum τ| / (r : ℝ) = |oneSum τ / (r : ℝ)| by rw [abs_div, abs_of_pos hrpos]]
                    exact abs_abs_sub_abs_le_abs_sub _ _
                  calc abs (|oneSum τ| / (r : ℝ) - û)
                      = |(|oneSum τ| / (r : ℝ) - |mGrid j|) + (|mGrid j| - u) + (u - û)| := by ring_nf
                    _ ≤ abs ((|oneSum τ| / (r : ℝ) - |mGrid j|) + (|mGrid j| - u)) + |u - û| :=
                        abs_add_le _ _
                    _ ≤ (abs (|oneSum τ| / (r : ℝ) - |mGrid j|) + abs (|mGrid j| - u)) + |u - û| :=
                        add_le_add (abs_add_le _ _) le_rfl
                    _ ≤ η + abs (|mGrid j| - u) + 1 / (r : ℝ) ^ 3 := by
                        rw [abs_sub_comm u û]
                        linarith
                have heq : |(|oneSum τ| / ((r : ℝ) * û) - 1)| = abs (|oneSum τ| / (r : ℝ) - û) / û := by
                  rw [show |oneSum τ| / ((r : ℝ) * û) - 1 = (|oneSum τ| / (r : ℝ) - û) / û by
                    field_simp [hû_pos.ne']]
                  rw [abs_div, abs_of_pos hû_pos]
                rw [heq]
                exact div_le_div_of_nonneg_right hnum hû_pos.le
              have hsq3 : δfn τ ^ 2 ≤
                  3 * (η ^ 2 + (|mGrid j| - u) ^ 2 + (1 / (r : ℝ) ^ 3) ^ 2) / û ^ 2 := by
                calc δfn τ ^ 2 = |δfn τ| ^ 2 := (sq_abs _).symm
                  _ ≤ ((η + abs (|mGrid j| - u) + 1 / (r : ℝ) ^ 3) / û) ^ 2 :=
                      pow_le_pow_left₀ (abs_nonneg _) htri 2
                  _ = (η + abs (|mGrid j| - u) + 1 / (r : ℝ) ^ 3) ^ 2 / û ^ 2 := by rw [div_pow]
                  _ ≤ 3 * (η ^ 2 + (abs (|mGrid j| - u)) ^ 2 + (1 / (r : ℝ) ^ 3) ^ 2) / û ^ 2 :=
                      div_le_div_of_nonneg_right (sq_three_sum_le _ _ _) (sq_nonneg _)
                  _ = 3 * (η ^ 2 + (|mGrid j| - u) ^ 2 + (1 / (r : ℝ) ^ 3) ^ 2) / û ^ 2 := by
                      rw [sq_abs]
              have hΛ3 : 3 * Λ / û ^ 2 ≤ c_loc * (r : ℝ) * θ := by
                rw [div_le_iff₀ (sq_pos_of_pos hû_pos)]
                linarith
              have hcθ_le : c_loc * θ ≤ 1 := by
                have h1 : θ * (c_loc + 1) ≤ 1 :=
                  (le_div_iff₀ (by positivity : (0 : ℝ) < c_loc + 1)).mp hθ_le_c
                nlinarith only [h1, hθ_pos]
              have ht1 : c_loc * (r : ℝ) * θ * η ^ 2 ≤ 1 := by
                have hη_sq : η ^ 2 ≤ (1 / ((r : ℝ) * Cmid)) ^ 2 :=
                  pow_le_pow_left₀ hη_pos.le hη_le 2
                have hr_inv : (r : ℝ) * (1 / ((r : ℝ) * Cmid)) ^ 2 ≤ 1 := by
                  have hCmid_ge1 : 1 ≤ Cmid := by dsimp [Cmid]; linarith [tau_pos S, hTmax_pos, hθ₁_pos]
                  rw [div_pow, one_pow, mul_pow]
                  rw [show (r : ℝ) * (1 / ((r : ℝ) ^ 2 * Cmid ^ 2)) = 1 / ((r : ℝ) * Cmid ^ 2) by
                    field_simp [hrpos.ne']]
                  rw [div_le_one (by positivity)]
                  nlinarith only [hCmid_ge1, show (1 : ℝ) ≤ (r : ℝ) by exact_mod_cast hr]
                calc c_loc * (r : ℝ) * θ * η ^ 2 = (c_loc * θ) * ((r : ℝ) * η ^ 2) := by ring
                  _ ≤ 1 * ((r : ℝ) * (1 / ((r : ℝ) * Cmid)) ^ 2) := by
                      gcongr
                  _ ≤ 1 * 1 := by linarith
                  _ = 1 := one_mul 1
              have ht3 : c_loc * (r : ℝ) * θ * (1 / (r : ℝ) ^ 3) ^ 2 ≤ 1 := by
                have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
                have h1 : (r : ℝ) * (1 / (r : ℝ) ^ 3) ^ 2 ≤ 1 := by
                  rw [div_pow, one_pow, show (r : ℝ) * (1 / ((r : ℝ) ^ 3) ^ 2) = 1 / (r : ℝ) ^ 5 by
                    field_simp [hrpos.ne']]
                  rw [div_le_one (by positivity)]
                  exact one_le_pow₀ hr1
                calc c_loc * (r : ℝ) * θ * (1 / (r : ℝ) ^ 3) ^ 2
                    = (c_loc * θ) * ((r : ℝ) * (1 / (r : ℝ) ^ 3) ^ 2) := by ring
                  _ ≤ 1 * 1 := mul_le_mul hcθ_le h1 (by positivity) zero_le_one
                  _ = 1 := one_mul 1
              calc Λ * δfn τ ^ 2
                  ≤ Λ * (3 * (η ^ 2 + (|mGrid j| - u) ^ 2 + (1 / (r : ℝ) ^ 3) ^ 2) / û ^ 2) :=
                      mul_le_mul_of_nonneg_left hsq3 hΛ_nn
                _ = (3 * Λ / û ^ 2) * (η ^ 2 + (|mGrid j| - u) ^ 2 + (1 / (r : ℝ) ^ 3) ^ 2) := by ring
                _ ≤ (c_loc * (r : ℝ) * θ) * (η ^ 2 + (|mGrid j| - u) ^ 2 + (1 / (r : ℝ) ^ 3) ^ 2) :=
                    mul_le_mul_of_nonneg_right hΛ3 (by positivity)
                _ = c_loc * (r : ℝ) * θ * η ^ 2 + (r : ℝ) * (c_loc * θ * (|mGrid j| - u) ^ 2) +
                      c_loc * (r : ℝ) * θ * (1 / (r : ℝ) ^ 3) ^ 2 := by ring
                _ ≤ 1 + (r : ℝ) * (Ftheta S θ u - Ftheta S θ (mGrid j)) + 1 := by
                    have hmid := mul_le_mul_of_nonneg_left hFmj hrpos.le
                    linarith
                _ = (r : ℝ) * (Ftheta S θ u - Ftheta S θ (mGrid j)) + 2 := by ring
            have hB : ∑ τ ∈ Ej, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) ≤
                ∑ τ ∈ Ej, (∏ α : Fin r, tilt S tj (τ α : ℚ)) * Real.exp ((r : ℝ) * Ftheta S θ u + 3) := by
              refine Finset.sum_le_sum fun τ hτ => ?_
              rw [cloudWeight_eq_tilt S β tj τ, mul_assoc, ← Real.exp_add]
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Finset.prod_nonneg fun α _ => by
                unfold tilt
                have := (S.pos _ (τ α).2).le
                positivity)
              have hmid := (Finset.mem_filter.mp (Finset.mem_filter.mp hτ).1).2
              have hbin := (Finset.mem_filter.mp hτ).2
              have hFdiff : (r : ℝ) * phi S tj - tj * oneSum τ + β / (2 * (r : ℝ)) * oneSum τ ^ 2 ≤
                  (r : ℝ) * Ftheta S θ (mGrid j) + 1 := by
                have hid : (r : ℝ) * phi S tj - tj * oneSum τ + β / (2 * (r : ℝ)) * oneSum τ ^ 2 -
                    (r : ℝ) * Ftheta S θ (mGrid j) =
                    (r : ℝ) * (tj * (mGrid j - oneSum τ / (r : ℝ)) +
                      (β / 2) * ((oneSum τ / (r : ℝ)) ^ 2 - mGrid j ^ 2)) := by
                  unfold Ftheta
                  rw [htj_rate]
                  dsimp [β]
                  field_simp [hrpos.ne']
                  ring
                have hlin : |tj * (mGrid j - oneSum τ / (r : ℝ)) +
                      (β / 2) * ((oneSum τ / (r : ℝ)) ^ 2 - mGrid j ^ 2)| ≤ Cmid * η := by
                  have ht_le : |tj| ≤ Tmax := abs_le.mpr ⟨htj_lo, htj_hi⟩
                  have hβ_pos : 0 < β := add_pos (tau_pos S) hθ_pos
                  have hβ_le : β ≤ tau S + θ₁ := by dsimp [β]; linarith
                  have hsum_abs : |oneSum τ / (r : ℝ) + mGrid j| ≤ 1 := by
                    calc |oneSum τ / (r : ℝ) + mGrid j| ≤ |oneSum τ / (r : ℝ)| + |mGrid j| := abs_add_le _ _
                      _ ≤ 1 / 2 + 1 / 2 := add_le_add hmid
                          (abs_le.mpr ⟨by linarith [(hmGrid_abs j).1], (hmGrid_abs j).2⟩)
                      _ = 1 := by norm_num
                  have hsq_diff : |(oneSum τ / (r : ℝ)) ^ 2 - mGrid j ^ 2| ≤ |oneSum τ / (r : ℝ) - mGrid j| := by
                    rw [show (oneSum τ / (r : ℝ)) ^ 2 - mGrid j ^ 2 =
                        (oneSum τ / (r : ℝ) + mGrid j) * (oneSum τ / (r : ℝ) - mGrid j) by ring, abs_mul]
                    exact mul_le_of_le_one_left (abs_nonneg _) hsum_abs
                  calc |tj * (mGrid j - oneSum τ / (r : ℝ)) +
                          (β / 2) * ((oneSum τ / (r : ℝ)) ^ 2 - mGrid j ^ 2)|
                      ≤ |tj| * |mGrid j - oneSum τ / (r : ℝ)| +
                          (β / 2) * |(oneSum τ / (r : ℝ)) ^ 2 - mGrid j ^ 2| :=
                          (abs_add_le _ _).trans (by rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < β / 2)])
                    _ ≤ Tmax * η + (β / 2) * η := by
                        rw [abs_sub_comm]
                        gcongr
                        exact le_trans hsq_diff hbin
                    _ ≤ Cmid * η := by
                        rw [← add_mul]
                        exact mul_le_mul_of_nonneg_right (by dsimp [Cmid]; linarith) hη_pos.le
                have hCmid_bnd : (r : ℝ) * (Cmid * η) ≤ 1 := by
                  calc (r : ℝ) * (Cmid * η) ≤ (r : ℝ) * (Cmid * (1 / ((r : ℝ) * Cmid))) := by
                        gcongr
                    _ = 1 := by
                        field_simp [hrpos.ne', hCmid_pos.ne']
                have hle_abs := le_trans (le_abs_self _) hlin
                linarith [mul_le_mul_of_nonneg_left hle_abs hrpos.le]
              linarith [hδ_exp τ hτ]
            calc ∑ τ ∈ Ej, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)
                ≤ ∑ τ ∈ Ej, (∏ α : Fin r, tilt S tj (τ α : ℚ)) * Real.exp ((r : ℝ) * Ftheta S θ u + 3) := hB
              _ = (∑ τ ∈ Ej, ∏ α : Fin r, tilt S tj (τ α : ℚ)) * Real.exp ((r : ℝ) * Ftheta S θ u + 3) :=
                  (Finset.sum_mul _ _ _).symm
              _ ≤ (∑ τ : Config S (Fin r), ∏ α : Fin r, tilt S tj (τ α : ℚ)) *
                    Real.exp ((r : ℝ) * Ftheta S θ u + 3) := by
                  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
                  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Ej) fun τ _ _ =>
                    Finset.prod_nonneg fun α _ => by
                      unfold tilt; have := (S.pos _ (τ α).2).le; positivity
              _ = Real.exp ((r : ℝ) * Ftheta S θ u + 3) := by rw [sum_prod_tilt, one_mul]
      _ = ((K : ℝ) + 1) * Real.exp 3 * Real.exp ((r : ℝ) * Ftheta S θ u) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
              Real.exp_add]
            ring
  have htail_le1 : 2 * (s_cov.card : ℝ) * Real.exp (-((r : ℝ) * θ₁ / 128)) ≤ 1 := by
    have hr_ge : (2 * (s_cov.card : ℝ) + 1) * (128 / θ₁) ≤ (r : ℝ) := hr_big
    have hx_ge : 2 * (s_cov.card : ℝ) + 1 ≤ (r : ℝ) * θ₁ / 128 := by
      have hmul := mul_le_mul_of_nonneg_right hr_ge (by positivity : 0 ≤ θ₁ / 128)
      have heq1 : (2 * (s_cov.card : ℝ) + 1) * (128 / θ₁) * (θ₁ / 128) = 2 * (s_cov.card : ℝ) + 1 := by
        rw [mul_assoc, div_mul_div_comm, mul_comm 128 θ₁,
          div_self (mul_ne_zero hθ₁_pos.ne' (by norm_num)), mul_one]
      linarith
    have hexp_ge : 2 * (s_cov.card : ℝ) + 1 ≤ Real.exp ((r : ℝ) * θ₁ / 128) :=
      le_trans hx_ge (by linarith [Real.add_one_le_exp ((r : ℝ) * θ₁ / 128)])
    rw [Real.exp_neg]
    calc 2 * (s_cov.card : ℝ) * (Real.exp ((r : ℝ) * θ₁ / 128))⁻¹
        ≤ (2 * (s_cov.card : ℝ) + 1) * (Real.exp ((r : ℝ) * θ₁ / 128))⁻¹ := by
            refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ Real.exp ((r : ℝ) * θ₁ / 128) * (Real.exp ((r : ℝ) * θ₁ / 128))⁻¹ := by
            refine mul_le_mul_of_nonneg_right hexp_ge (by positivity)
      _ = 1 := mul_inv_cancel₀ (Real.exp_pos _).ne'
  have htotal_ratio :
      (∑ τ : Config S (Fin r), cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) /
        (∑ τ : Config S (Fin r), cloudWeight S β τ) ≤
      ((K : ℝ) + 1) * Real.exp 3 + 1 := by
    have hZ_ge1 : (1 : ℝ) ≤ Real.exp ((r : ℝ) * Ftheta S θ u) := by
      rw [Real.one_le_exp_iff]
      have hFu_nn : 0 ≤ Ftheta S θ u := by
        -- rateI at 0 is 0, and u maximizes Ftheta by Ftheta_le/gap? Actually hF_gap at m=0 gives c*θ*u^2 ≤ Ftheta u - Ftheta 0 = Ftheta u!
        have hg0 := hF_gap 0 (by norm_num)
        have hF0 : Ftheta S θ 0 = 0 := by unfold Ftheta; rw [rateI_zero]; ring
        have hnn : 0 ≤ c_loc * θ * (|(0 : ℝ)| - u) ^ 2 := by positivity
        linarith
      exact mul_nonneg hrpos.le hFu_nn
    have hnum_le :
        ∑ τ : Config S (Fin r), cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2) ≤
          (((K : ℝ) + 1) * Real.exp 3 + 1) * Real.exp ((r : ℝ) * Ftheta S θ u) := by
      calc ∑ τ : Config S (Fin r), cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)
          ≤ (∑ τ ∈ E_mid, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) +
            2 * (∑ τ ∈ E_hi, cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)) := by
              linarith [hsplit_sum, hE_lo_eq]
        _ ≤ ((K : ℝ) + 1) * Real.exp 3 * Real.exp ((r : ℝ) * Ftheta S θ u) +
              2 * ((s_cov.card : ℝ) * Real.exp (-((r : ℝ) * θ₁ / 128))) := by
              linarith [hE_mid_bound, hE_hi_bound]
        _ ≤ ((K : ℝ) + 1) * Real.exp 3 * Real.exp ((r : ℝ) * Ftheta S θ u) + 1 := by
              linarith [htail_le1]
        _ ≤ ((K : ℝ) + 1) * Real.exp 3 * Real.exp ((r : ℝ) * Ftheta S θ u) +
              1 * Real.exp ((r : ℝ) * Ftheta S θ u) := by linarith
        _ = (((K : ℝ) + 1) * Real.exp 3 + 1) * Real.exp ((r : ℝ) * Ftheta S θ u) := by ring
    rw [div_le_iff₀ hZ_pos]
    calc ∑ τ : Config S (Fin r), cloudWeight S β τ * Real.exp (Λ * δfn τ ^ 2)
        ≤ (((K : ℝ) + 1) * Real.exp 3 + 1) * Real.exp ((r : ℝ) * Ftheta S θ u) := hnum_le
      _ ≤ (((K : ℝ) + 1) * Real.exp 3 + 1) * ∑ τ : Config S (Fin r), cloudWeight S β τ :=
          mul_le_mul_of_nonneg_left hZ_ge (by positivity)
  have hK_poly : ((K : ℝ) + 1) * Real.exp 3 + 1 ≤ ((r : ℝ) + 1) ^ Kpow := by
    have hK1_le : (K : ℝ) + 1 ≤ (r : ℝ) * Cmid + 2 := by linarith
    have hr_ge1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hr1_ge2 : (2 : ℝ) ≤ (r : ℝ) + 1 := by linarith
    have h_lin : ((K : ℝ) + 1) * Real.exp 3 + 1 ≤ ((r : ℝ) + 1) * ((Cmid + 2) * Real.exp 3 + 1) := by
      have he : 0 < Real.exp 3 := Real.exp_pos 3
      calc ((K : ℝ) + 1) * Real.exp 3 + 1
          ≤ ((r : ℝ) * Cmid + 2) * Real.exp 3 + 1 := by linarith [mul_le_mul_of_nonneg_right hK1_le he.le]
        _ ≤ ((r : ℝ) + 1) * ((Cmid + 2) * Real.exp 3 + 1) := by nlinarith only [hCmid_pos, hr_ge1, he]
    have hpow_ge : (Cmid + 2) * Real.exp 3 + 1 ≤ ((r : ℝ) + 1) ^ (Kpow - 1) := by
      have hceil : (Cmid + 2) * Real.exp 3 + 1 ≤ (Nat.ceil ((Cmid + 2) * Real.exp 3 + 1) : ℝ) :=
        Nat.le_ceil _
      have hnat : Nat.ceil ((Cmid + 2) * Real.exp 3 + 1) ≤ 2 ^ (Kpow - 1) := by
        dsimp [Kpow]
        exact (Nat.lt_two_pow_self (n := Nat.ceil ((Cmid + 2) * Real.exp 3 + 1))).le
      have h2 : (Nat.ceil ((Cmid + 2) * Real.exp 3 + 1) : ℝ) ≤ (2 : ℝ) ^ (Kpow - 1) := by
        exact_mod_cast hnat
      have h2r : (2 : ℝ) ^ (Kpow - 1) ≤ ((r : ℝ) + 1) ^ (Kpow - 1) :=
        pow_le_pow_left₀ zero_le_two hr1_ge2 _
      exact le_trans hceil (le_trans h2 h2r)
    calc ((K : ℝ) + 1) * Real.exp 3 + 1
        ≤ ((r : ℝ) + 1) * ((Cmid + 2) * Real.exp 3 + 1) := h_lin
      _ ≤ ((r : ℝ) + 1) * ((r : ℝ) + 1) ^ (Kpow - 1) :=
          mul_le_mul_of_nonneg_left hpow_ge (by positivity)
      _ = ((r : ℝ) + 1) ^ Kpow := by
          have hKp : 1 ≤ Kpow := by dsimp [Kpow]; omega
          conv_rhs => rw [show Kpow = (Kpow - 1) + 1 by omega, pow_succ']
  exact le_trans htotal_ratio hK_poly

end SingleCloud

section MultiCloud

private def cfgSplitEquiv (S : SpinLaw) (n r : ℕ) :
    Config S (Fin n × Fin r) ≃ (Fin n → Config S (Fin r)) where
  toFun σ i α := σ (i, α)
  invFun f p := f p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

private lemma nuProd_nonneg (S : SpinLaw) (β : ℝ) {n r : ℕ} (y : BinCfg n)
    (σ : Config S (Fin n × Fin r)) : 0 ≤ nuProd S β y σ := by
  unfold nuProd
  exact Finset.prod_nonneg fun i _ => nuPm_nonneg S β (y i) (slice σ i)

private lemma nuProd_sum_prod (S : SpinLaw) (β : ℝ) (n r : ℕ) (y : BinCfg n)
    (f : Fin n → Config S (Fin r) → ℝ) :
    (∑ σ : Config S (Fin n × Fin r), nuProd S β y σ * ∏ i : Fin n, f i (slice σ i)) =
      ∏ i : Fin n, ∑ τ : Config S (Fin r), nuPm S β (y i) τ * f i τ := by
  have h1 : (∑ σ : Config S (Fin n × Fin r), nuProd S β y σ * ∏ i : Fin n, f i (slice σ i)) =
      ∑ σ : Config S (Fin n × Fin r), ∏ i : Fin n, (nuPm S β (y i) (slice σ i) * f i (slice σ i)) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    unfold nuProd
    rw [← Finset.prod_mul_distrib]
  rw [h1]
  have h2 : (∑ σ : Config S (Fin n × Fin r), ∏ i : Fin n, (nuPm S β (y i) (slice σ i) * f i (slice σ i))) =
      ∑ g : Fin n → Config S (Fin r), ∏ i : Fin n, (nuPm S β (y i) (g i) * f i (g i)) := by
    refine Fintype.sum_equiv (cfgSplitEquiv S n r) _ _ ?_
    intro σ
    rfl
  rw [h2]
  exact (Fintype.prod_sum (fun i τ => nuPm S β (y i) τ * f i τ)).symm

private lemma nuProd_sum_one (S : SpinLaw) (β : ℝ) (n r : ℕ) (y : BinCfg n) :
    (∑ σ : Config S (Fin n × Fin r), nuProd S β y σ) = 1 := by
  have h := nuProd_sum_prod S β n r y (fun _ _ => (1 : ℝ))
  simp only [Finset.prod_const_one, mul_one] at h
  rw [h]
  simp only [nuPm_sum_one, Finset.prod_const_one]

private lemma nuProd_ne_zero_sign (S : SpinLaw) (β : ℝ) {n r : ℕ} (y : BinCfg n)
    (σ : Config S (Fin n × Fin r)) (hσ : nuProd S β y σ ≠ 0) (i : Fin n) :
    0 ≤ spinOf (y i) * cloudSum σ i := by
  by_contra hlt
  push_neg at hlt
  have hz : nuPm S β (y i) (slice σ i) = 0 := by
    unfold nuPm
    change cloudWeight S β (slice σ i) / zPlus S β r *
      ((if 0 < spinOf (y i) * cloudSum σ i then (1 : ℝ) else 0) +
        (1 / 2) * (if cloudSum σ i = 0 then (1 : ℝ) else 0)) = 0
    have hc0 : cloudSum σ i ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hlt
      exact lt_irrefl _ hlt
    simp [hlt.not_gt, hc0]
  have hp0 : nuProd S β y σ = 0 := by
    unfold nuProd
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz
  exact hσ hp0

private lemma abs_spinOf (b : Bool) : |spinOf b| = 1 := by
  cases b <;> simp [spinOf]

private lemma spinOf_mul_abs_eq (b : Bool) (x : ℝ) (hx : 0 ≤ spinOf b * x) :
    spinOf b * |x| = x := by
  cases b
  · simp only [spinOf, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul] at hx ⊢
    have hx0 : x ≤ 0 := by linarith
    rw [abs_of_nonpos hx0]
    ring
  · simp only [spinOf, ↓reduceIte, one_mul] at hx ⊢
    exact abs_of_nonneg hx

private lemma dy_abs_bound {S : SpinLaw} {n r : ℕ} (hn : 1 ≤ n)
    (J₀ : Matrix (Fin n) (Fin n) ℝ) (hSymm : J₀.IsSymm) (h₀ : Fin n → ℝ) (û : ℝ)
    (hû_pos : 0 < û) (hr_pos : (0 : ℝ) < r)
    (y : BinCfg n) (σ : Config S (Fin n × Fin r))
    (hsign : ∀ i : Fin n, 0 ≤ spinOf (y i) * cloudSum σ i) :
    let W := max 1 (width J₀ h₀)
    let δ : Fin n → ℝ := fun i => |cloudSum σ i| / ((r : ℝ) * û) - 1
    |Dy J₀ h₀ û y σ| ≤ 1 / 4 + (3 / 2) * (n : ℝ) * W ^ 2 * ∑ i : Fin n, δ i ^ 2 := by
  intro W δ
  let s : Fin n → ℝ := binVec y
  let Δ : Fin n → ℝ := fun i => s i * δ i
  have hvec : (fun i => cloudSum σ i / ((r : ℝ) * û)) = (fun i => s i + Δ i) := by
    funext i
    dsimp [s, binVec, Δ, δ]
    have hmul := spinOf_mul_abs_eq (y i) (cloudSum σ i) (hsign i)
    calc cloudSum σ i / ((r : ℝ) * û)
        = (spinOf (y i) * |cloudSum σ i|) / ((r : ℝ) * û) := by rw [hmul]
      _ = spinOf (y i) * (1 + (|cloudSum σ i| / ((r : ℝ) * û) - 1)) := by ring
      _ = spinOf (y i) + spinOf (y i) * (|cloudSum σ i| / ((r : ℝ) * û) - 1) := by ring
  have hDy_eq : Dy J₀ h₀ û y σ =
      ∑ i : Fin n, Δ i * (h₀ i + ∑ j : Fin n, J₀ i j * s j) +
      (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, J₀ i j * Δ i * Δ j := by
    unfold Dy energy
    rw [hvec]
    have hcross : ∑ i : Fin n, ∑ j : Fin n, J₀ i j * (s i * Δ j) =
        ∑ i : Fin n, ∑ j : Fin n, J₀ i j * (Δ i * s j) := by
      calc ∑ i : Fin n, ∑ j : Fin n, J₀ i j * (s i * Δ j)
          = ∑ j : Fin n, ∑ i : Fin n, J₀ i j * (s i * Δ j) := Finset.sum_comm
        _ = ∑ j : Fin n, ∑ i : Fin n, J₀ j i * (Δ j * s i) := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
            have hji : J₀ j i = J₀ i j := congrFun (congrFun hSymm i) j
            rw [hji]; ring
    have hquad_exp :
        ∑ i : Fin n, ∑ j : Fin n, J₀ i j * (s i + Δ i) * (s j + Δ j) -
        ∑ i : Fin n, ∑ j : Fin n, J₀ i j * s i * s j =
        2 * ∑ i : Fin n, Δ i * ∑ j : Fin n, J₀ i j * s j +
        ∑ i : Fin n, ∑ j : Fin n, J₀ i j * Δ i * Δ j := by
      rw [← Finset.sum_sub_distrib]
      have h1 : ∀ i : Fin n,
          (∑ j : Fin n, J₀ i j * (s i + Δ i) * (s j + Δ j) - ∑ j : Fin n, J₀ i j * s i * s j) =
          ∑ j : Fin n, (J₀ i j * (Δ i * s j) + J₀ i j * (s i * Δ j) + J₀ i j * Δ i * Δ j) := by
        intro i
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      simp_rw [h1, Finset.sum_add_distrib]
      rw [hcross]
      have hrow : ∑ i : Fin n, ∑ j : Fin n, J₀ i j * (Δ i * s j) =
          ∑ i : Fin n, Δ i * ∑ j : Fin n, J₀ i j * s j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hrow]
      ring
    have hlin_sub : ∑ i : Fin n, h₀ i * (s i + Δ i) - ∑ i : Fin n, h₀ i * s i =
        ∑ i : Fin n, Δ i * h₀ i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    calc (1 / 2 * ∑ i, ∑ j, J₀ i j * (s i + Δ i) * (s j + Δ j) + ∑ i, h₀ i * (s i + Δ i)) -
          (1 / 2 * ∑ i, ∑ j, J₀ i j * s i * s j + ∑ i, h₀ i * s i)
        = (1 / 2) * (∑ i, ∑ j, J₀ i j * (s i + Δ i) * (s j + Δ j) - ∑ i, ∑ j, J₀ i j * s i * s j) +
            (∑ i, h₀ i * (s i + Δ i) - ∑ i, h₀ i * s i) := by ring
      _ = (1 / 2) * (2 * ∑ i, Δ i * ∑ j, J₀ i j * s j + ∑ i, ∑ j, J₀ i j * Δ i * Δ j) +
            ∑ i, Δ i * h₀ i := by rw [hquad_exp, hlin_sub]
      _ = (∑ i, Δ i * ∑ j, J₀ i j * s j + ∑ i, Δ i * h₀ i) +
            (1 / 2) * ∑ i, ∑ j, J₀ i j * Δ i * Δ j := by ring
      _ = (∑ i, Δ i * (h₀ i + ∑ j, J₀ i j * s j)) +
            (1 / 2) * ∑ i, ∑ j, J₀ i j * Δ i * Δ j := by
          rw [← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ => by ring
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hW_row : ∀ i : Fin n, |h₀ i| + ∑ j : Fin n, |J₀ i j| ≤ W := by
    intro i
    have hle : |h₀ i| + ∑ j : Fin n, |J₀ i j| ≤ width J₀ h₀ := by
      unfold width
      exact le_ciSup (Finite.bddAbove_range (fun k : Fin n => |h₀ k| + ∑ j : Fin n, |J₀ k j|)) i
    exact le_trans hle (le_max_right _ _)
  have hW_col : ∀ j : Fin n, ∑ i : Fin n, |J₀ i j| ≤ W := by
    intro j
    have hsum : ∑ i : Fin n, |J₀ i j| = ∑ i : Fin n, |J₀ j i| := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show J₀ i j = J₀ j i from (congrFun (congrFun hSymm i) j).symm]
    rw [hsum]
    exact le_trans (by linarith [abs_nonneg (h₀ j)]) (hW_row j)
  have hW_rowJ : ∀ i : Fin n, ∑ j : Fin n, |J₀ i j| ≤ W := fun i =>
    le_trans (by linarith [abs_nonneg (h₀ i)]) (hW_row i)
  have hlin_bnd : |∑ i : Fin n, Δ i * (h₀ i + ∑ j : Fin n, J₀ i j * s j)| ≤ W * ∑ i : Fin n, |δ i| := by
    calc |∑ i : Fin n, Δ i * (h₀ i + ∑ j : Fin n, J₀ i j * s j)|
        ≤ ∑ i : Fin n, |Δ i * (h₀ i + ∑ j : Fin n, J₀ i j * s j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, |δ i| * W := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hΔ : |Δ i| = |δ i| := by dsimp [Δ, s, binVec]; rw [abs_mul, abs_spinOf, one_mul]
          have hc : |h₀ i + ∑ j : Fin n, J₀ i j * s j| ≤ W := by
            calc |h₀ i + ∑ j : Fin n, J₀ i j * s j|
                ≤ |h₀ i| + |∑ j : Fin n, J₀ i j * s j| := abs_add_le _ _
              _ ≤ |h₀ i| + ∑ j : Fin n, |J₀ i j * s j| := add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
              _ = |h₀ i| + ∑ j : Fin n, |J₀ i j| := by
                  congr 1
                  refine Finset.sum_congr rfl fun j _ => ?_
                  dsimp [s, binVec]
                  rw [abs_mul, abs_spinOf, mul_one]
              _ ≤ W := hW_row i
          rw [abs_mul, hΔ]
          exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
      _ = W * ∑ i : Fin n, |δ i| := by rw [← Finset.sum_mul, mul_comm]
  have hquad_bnd : |(1 / 2) * ∑ i : Fin n, ∑ j : Fin n, J₀ i j * Δ i * Δ j| ≤
      (W / 2) * ∑ i : Fin n, δ i ^ 2 := by
    have hΔsq : ∀ i : Fin n, Δ i ^ 2 = δ i ^ 2 := fun i => by
      dsimp [Δ, s, binVec]
      rw [mul_pow, ← sq_abs (spinOf (y i)), abs_spinOf, one_pow, one_mul]
    calc |(1 / 2) * ∑ i : Fin n, ∑ j : Fin n, J₀ i j * Δ i * Δ j|
        = (1 / 2) * |∑ i : Fin n, ∑ j : Fin n, J₀ i j * Δ i * Δ j| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      _ ≤ (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, |J₀ i j * Δ i * Δ j| := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, |J₀ i j| * ((Δ i ^ 2 + Δ j ^ 2) / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul, abs_mul, mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            nlinarith only [sq_nonneg (|Δ i| - |Δ j|), sq_abs (Δ i), sq_abs (Δ j)]
      _ = (1 / 4) * (∑ i : Fin n, (∑ j : Fin n, |J₀ i j|) * Δ i ^ 2 +
            ∑ j : Fin n, (∑ i : Fin n, |J₀ i j|) * Δ j ^ 2) := by
            have ha : ∑ i : Fin n, ∑ j : Fin n, |J₀ i j| * ((Δ i ^ 2 + Δ j ^ 2) / 2) =
                (1 / 2) * (∑ i : Fin n, (∑ j : Fin n, |J₀ i j|) * Δ i ^ 2 +
                  ∑ j : Fin n, (∑ i : Fin n, |J₀ i j|) * Δ j ^ 2) := by
              have hsplit : ∑ i : Fin n, ∑ j : Fin n, |J₀ i j| * ((Δ i ^ 2 + Δ j ^ 2) / 2) =
                  (1 / 2) * (∑ i : Fin n, ∑ j : Fin n, |J₀ i j| * Δ i ^ 2 +
                    ∑ i : Fin n, ∑ j : Fin n, |J₀ i j| * Δ j ^ 2) := by
                rw [← Finset.sum_add_distrib, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [← Finset.sum_add_distrib, Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => by ring
              rw [hsplit]
              congr 1
              congr 1
              · refine Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
              · rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
            rw [ha]; ring
      _ ≤ (1 / 4) * (W * ∑ i : Fin n, δ i ^ 2 + W * ∑ j : Fin n, δ j ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            refine add_le_add ?_ ?_
            · rw [Finset.mul_sum]
              refine Finset.sum_le_sum fun i _ => by
                rw [hΔsq i]
                exact mul_le_mul_of_nonneg_right (hW_rowJ i) (sq_nonneg _)
            · rw [Finset.mul_sum]
              refine Finset.sum_le_sum fun j _ => by
                rw [hΔsq j]
                exact mul_le_mul_of_nonneg_right (hW_col j) (sq_nonneg _)
      _ = (W / 2) * ∑ i : Fin n, δ i ^ 2 := by ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ge1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hW_ge1 : 1 ≤ W := le_max_left _ _
  have ham : W * ∑ i : Fin n, |δ i| ≤ 1 / 4 + (n : ℝ) * W ^ 2 * ∑ i : Fin n, δ i ^ 2 := by
    have hpt : ∀ i : Fin n, W * |δ i| ≤ 1 / (4 * (n : ℝ)) + (n : ℝ) * W ^ 2 * δ i ^ 2 := by
      intro i
      have hsq : 0 ≤ (1 - 2 * (n : ℝ) * W * |δ i|) ^ 2 := sq_nonneg _
      have h1 : 4 * (n : ℝ) * W * |δ i| ≤ 1 + 4 * (n : ℝ) ^ 2 * W ^ 2 * δ i ^ 2 := by
        have hsq_eq : (1 - 2 * (n : ℝ) * W * |δ i|) ^ 2 =
            1 - 4 * (n : ℝ) * W * |δ i| + 4 * (n : ℝ) ^ 2 * W ^ 2 * δ i ^ 2 := by
          rw [sub_sq, mul_pow, mul_pow, mul_pow, sq_abs]; ring
        linarith
      have hd := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 4 * (n : ℝ))
      have hL : (4 * (n : ℝ) * W * |δ i|) / (4 * (n : ℝ)) = W * |δ i| := by
        field_simp [hnpos.ne']
      have hR : (1 + 4 * (n : ℝ) ^ 2 * W ^ 2 * δ i ^ 2) / (4 * (n : ℝ)) =
          1 / (4 * (n : ℝ)) + (n : ℝ) * W ^ 2 * δ i ^ 2 := by
        field_simp [hnpos.ne']
      linarith
    calc W * ∑ i : Fin n, |δ i| = ∑ i : Fin n, W * |δ i| := Finset.mul_sum _ _ _
      _ ≤ ∑ i : Fin n, (1 / (4 * (n : ℝ)) + (n : ℝ) * W ^ 2 * δ i ^ 2) := Finset.sum_le_sum fun i _ => hpt i
      _ = (n : ℝ) * (1 / (4 * (n : ℝ))) + (n : ℝ) * W ^ 2 * ∑ i : Fin n, δ i ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
      _ = 1 / 4 + (n : ℝ) * W ^ 2 * ∑ i : Fin n, δ i ^ 2 := by
          field_simp [hnpos.ne']
  have hW_half : (W / 2) * ∑ i : Fin n, δ i ^ 2 ≤ ((n : ℝ) * W ^ 2 / 2) * ∑ i : Fin n, δ i ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    nlinarith only [hn_ge1, hW_ge1]
  calc |Dy J₀ h₀ û y σ|
      ≤ |∑ i : Fin n, Δ i * (h₀ i + ∑ j : Fin n, J₀ i j * s j)| +
          |(1 / 2) * ∑ i : Fin n, ∑ j : Fin n, J₀ i j * Δ i * Δ j| := by
          rw [hDy_eq]; exact abs_add_le _ _
    _ ≤ W * ∑ i : Fin n, |δ i| + (W / 2) * ∑ i : Fin n, δ i ^ 2 := add_le_add hlin_bnd hquad_bnd
    _ ≤ 1 / 4 + (n : ℝ) * W ^ 2 * ∑ i : Fin n, δ i ^ 2 +
          ((n : ℝ) * W ^ 2 / 2) * ∑ i : Fin n, δ i ^ 2 := add_le_add ham hW_half
    _ = 1 / 4 + (3 / 2) * (n : ℝ) * W ^ 2 * ∑ i : Fin n, δ i ^ 2 := by ring

end MultiCloud

end P6c

open P6c

theorem solution (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) (hP : ∀ (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p), ∃ θ₀ c C : ℝ, 0 < θ₀ ∧ 0 < c ∧ 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∃ u : ℝ, (0 < u ∧ u < 1 ∧ u = deriv (phi S) ((tau S + θ) * u)) ∧
        (∀ u' : ℝ, 0 < u' → u' < 1 → u' = deriv (phi S) ((tau S + θ) * u') → u' = u) ∧
        c * θ ^ (1 / (2 * (p : ℝ) - 2)) ≤ u ∧ u ≤ C * θ ^ (1 / (2 * (p : ℝ) - 2)) ∧
        c * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) ≤ θ * u ^ 2 ∧
        θ * u ^ 2 ≤ C * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) ∧
        Ftheta S θ (-u) = Ftheta S θ u ∧
        (∀ m : ℝ, |m| ≤ 1 → Ftheta S θ m ≤ Ftheta S θ u) ∧
        (∀ m : ℝ, |m| ≤ 1 → c * θ * (|m| - u) ^ 2 ≤ Ftheta S θ u - Ftheta S θ m)) :
    ∃ θ₀ Cₛ : ℝ, 0 < θ₀ ∧ 0 < Cₛ ∧
      ∀ (n r : ℕ) (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (θ : ℝ) (û : ℚ) (L : ℝ),
        1 ≤ n → 1 ≤ r → J₀.IsSymm → (∀ i, J₀ i i = 0) → 0 < θ → θ ≤ θ₀ → IsUhat S θ r û →
        (n : ℝ) ≤ L →
        (r : ℝ) * θ * (û : ℝ) ^ 2 ≥
          Cₛ * (n : ℝ) * (max 1 (width J₀ h₀)) ^ 2 *
            ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1) →
        ∀ y : BinCfg n,
          (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              (open Classical in if ∃ i, cloudSum σ i = 0 then (1 : ℝ) else 0)) ≤ Real.exp (-L) ∧
          (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              (Real.exp |Dy J₀ h₀ (û : ℝ) y σ| *
                (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0))) ≤ Real.exp (-L) ∧
          Real.exp (-1) * (1 - Real.exp (-L)) ≤
            (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              Real.exp (Dy J₀ h₀ (û : ℝ) y σ)) ∧
          (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              Real.exp (Dy J₀ h₀ (û : ℝ) y σ)) ≤ Real.exp 1 + Real.exp (-L) := by
  obtain ⟨θ₀_loc, c_loc, C_loc, hθ₀_pos, hc_loc_pos, hC_loc_pos, hprop⟩ := hP S p hS hp
  obtain ⟨Tmax, hTmax_pos, hTmax_val⟩ := deriv_phi_large S
  obtain ⟨θ₁, s_cov, hθ₁_pos, hθ₁_le_loc, hcov⟩ :=
    tail_compact_cover S p hS hp θ₀_loc c_loc C_loc hθ₀_pos hc_loc_pos hC_loc_pos hprop
  obtain ⟨θ₀_cap, Kpow, hθ₀_cap_pos, hθ₀_cap_le, hexp_cap⟩ :=
    exp_moment_single_cloud S p hS Tmax hTmax_pos hTmax_val θ₁ c_loc hθ₁_pos hc_loc_pos s_cov hcov
  let Rmin : ℝ := (2 * (s_cov.card : ℝ) + 1) * (128 / θ₁)
  let Cₛ : ℝ := max (8 / c_loc) (max (4 * θ₀_cap * Rmin) (3 * (3 / 2 + 2 * ((Kpow : ℝ) + 2)) / c_loc))
  refine ⟨θ₀_cap, Cₛ, hθ₀_cap_pos, lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  intro n r J₀ h₀ θ û L hn hr hSymm _ hθ_pos hθ_le hUhat hnL hcond y
  have hθ_le_loc : θ ≤ θ₀_loc := le_trans hθ_le (le_trans hθ₀_cap_le hθ₁_le_loc)
  obtain ⟨u, hu_fp, huniq, _, _, _, _, _, hmax_u, hgap_u⟩ := hprop θ hθ_pos hθ_le_loc
  obtain ⟨u', hu'_pos, hu'_lt1, hu'_fp, hû_diff, hû_lo, hû_hi⟩ := hUhat
  have hu_eq : u' = u := huniq u' hu'_pos hu'_lt1 hu'_fp
  subst hu_eq
  have hu_abs : |u'| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu'_pos, hu'_lt1]
  have hû_pos : 0 < (û : ℝ) := lt_of_lt_of_le (by positivity) hû_lo
  have hW_ge1 : 1 ≤ max 1 (width J₀ h₀) := le_max_left _ _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hn_ge1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr_ge1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hL_ge1 : 1 ≤ L := le_trans hn_ge1 hnL
  have hlog_nn : 0 ≤ Real.log ((r : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hfactor_ge1 : 1 ≤ (n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1 := by
    nlinarith only [hnpos, hlog_nn, hL_ge1]
  have hr_big : Rmin ≤ (r : ℝ) := by
    have h4 : (û : ℝ) ^ 2 ≤ 4 := by
      have hle2 : (û : ℝ) ≤ 2 := by linarith [hu_fp.2.1]
      nlinarith only [hle2, hû_pos]
    have hCs : 4 * θ₀_cap * Rmin ≤ Cₛ := le_trans (le_max_left _ _) (le_max_right _ _)
    have h1 : 4 * θ₀_cap * Rmin ≤ (r : ℝ) * θ * (û : ℝ) ^ 2 := by
      have hnl : 1 ≤ (n : ℝ) * (max 1 (width J₀ h₀)) ^ 2 := by nlinarith only [hn_ge1, hW_ge1]
      calc 4 * θ₀_cap * Rmin ≤ Cₛ := hCs
        _ ≤ Cₛ * ((n : ℝ) * (max 1 (width J₀ h₀)) ^ 2 * ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1)) := by
            refine le_mul_of_one_le_right (by positivity) ?_
            nlinarith only [hnl, hfactor_ge1]
        _ ≤ (r : ℝ) * θ * (û : ℝ) ^ 2 := by linarith [hcond]
    have h2 : (r : ℝ) * θ * (û : ℝ) ^ 2 ≤ (r : ℝ) * (4 * θ₀_cap) := by
      have hθu : θ * (û : ℝ) ^ 2 ≤ θ₀_cap * 4 := mul_le_mul hθ_le h4 (sq_nonneg _) hθ₀_cap_pos.le
      nlinarith only [hθu, hrpos]
    nlinarith only [h1, h2, hθ₀_cap_pos]
  have hPart1 :
      (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
          (open Classical in if ∃ i, cloudSum σ i = 0 then (1 : ℝ) else 0)) ≤ Real.exp (-L) := by
    have hunion : ∀ σ : Config S (Fin n × Fin r),
        (open Classical in if ∃ i, cloudSum σ i = 0 then (1 : ℝ) else 0) ≤
          ∑ i : Fin n, (if cloudSum σ i = 0 then (1 : ℝ) else 0) := by
      intro σ
      by_cases h : ∃ i, cloudSum σ i = 0
      · obtain ⟨i₀, hi₀⟩ := h
        rw [if_pos ⟨i₀, hi₀⟩]
        have hge0 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
            (0 : ℝ) ≤ if cloudSum σ i = 0 then 1 else 0 := fun i _ => by split_ifs <;> norm_num
        calc (1 : ℝ) = (if cloudSum σ i₀ = 0 then (1 : ℝ) else 0) := by simp [hi₀]
          _ ≤ ∑ i : Fin n, (if cloudSum σ i = 0 then (1 : ℝ) else 0) :=
            Finset.single_le_sum hge0 (Finset.mem_univ i₀)
      · rw [if_neg h]
        exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
    have hstep1 :
        ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
            (open Classical in if ∃ i, cloudSum σ i = 0 then (1 : ℝ) else 0) ≤
          ∑ i : Fin n, ∑ σ : Config S (Fin n × Fin r),
            nuProd S (tau S + θ) y σ * (if cloudSum σ i = 0 then (1 : ℝ) else 0) := by
      calc ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              (open Classical in if ∃ i, cloudSum σ i = 0 then (1 : ℝ) else 0)
          ≤ ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              ∑ i : Fin n, (if cloudSum σ i = 0 then (1 : ℝ) else 0) :=
              Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hunion σ) (nuProd_nonneg _ _ _ _)
        _ = ∑ σ : Config S (Fin n × Fin r), ∑ i : Fin n,
              nuProd S (tau S + θ) y σ * (if cloudSum σ i = 0 then (1 : ℝ) else 0) := by
              refine Finset.sum_congr rfl fun σ _ => Finset.mul_sum _ _ _
        _ = _ := Finset.sum_comm
    have heach : ∀ i : Fin n,
        ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ * (if cloudSum σ i = 0 then (1 : ℝ) else 0) ≤
          Real.exp (-((r : ℝ) * Ftheta S θ u')) := by
      intro i
      have hfactor := nuProd_sum_prod S (tau S + θ) n r y
        (fun j τ => if j = i then (if oneSum τ = 0 then (1 : ℝ) else 0) else 1)
      have hL : (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
            ∏ j : Fin n, (if j = i then (if oneSum (slice σ j) = 0 then (1 : ℝ) else 0) else (1 : ℝ))) =
          ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
            (if cloudSum σ i = 0 then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        congr 1
        rw [Finset.prod_eq_single i]
        · simp only [↓reduceIte]; rfl
        · intro j _ hj; simp [hj]
        · intro hi; exact (hi (Finset.mem_univ i)).elim
      rw [← hL, hfactor]
      have hR : (∏ j : Fin n, ∑ τ : Config S (Fin r),
            nuPm S (tau S + θ) (y j) τ * (if j = i then (if oneSum τ = 0 then (1 : ℝ) else 0) else (1 : ℝ))) =
          ∑ τ : Config S (Fin r), nuPm S (tau S + θ) (y i) τ * (if oneSum τ = 0 then (1 : ℝ) else 0) := by
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hj
          simp [hj, nuPm_sum_one]
        · intro hi; exact (hi (Finset.mem_univ i)).elim
      rw [hR]
      exact zero_sum_single_le S θ u' r (y i) hr hθ_pos hu_abs hu_fp.2.2
    have hF_lower : 2 * L ≤ (r : ℝ) * Ftheta S θ u' := by
      have hF0 : Ftheta S θ 0 = 0 := by unfold Ftheta; rw [rateI_zero]; ring
      have hgap0 := hgap_u 0 (by norm_num)
      rw [hF0, sub_zero, abs_zero, zero_sub, neg_sq] at hgap0
      have hCs1 : 8 / c_loc ≤ Cₛ := le_max_left _ _
      have h1 : (r : ℝ) * θ * (û : ℝ) ^ 2 ≥ (8 / c_loc) * L := by
        calc (r : ℝ) * θ * (û : ℝ) ^ 2
            ≥ Cₛ * ((n : ℝ) * (max 1 (width J₀ h₀)) ^ 2 * ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1)) := by
                linarith [hcond]
          _ ≥ (8 / c_loc) * (1 * L) := by
                have ha : 1 ≤ (n : ℝ) * (max 1 (width J₀ h₀)) ^ 2 := by nlinarith only [hn_ge1, hW_ge1]
                have hb : L ≤ (n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1 := by linarith [mul_nonneg hnpos.le hlog_nn]
                have hprod : 1 * L ≤ ((n : ℝ) * (max 1 (width J₀ h₀)) ^ 2) *
                    ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1) :=
                  mul_le_mul ha hb (by linarith) (by positivity)
                exact mul_le_mul hCs1 hprod (by positivity) (by positivity)
          _ = (8 / c_loc) * L := by ring
      have h2 : 8 * L ≤ c_loc * (r : ℝ) * θ * (û : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_left h1 hc_loc_pos.le
        have heq : c_loc * ((8 / c_loc) * L) = 8 * L := by field_simp [hc_loc_pos.ne']
        linarith
      have h3 : (û : ℝ) ^ 2 ≤ 4 * u' ^ 2 := by
        have := pow_le_pow_left₀ hû_pos.le hû_hi 2
        linarith [show (2 * u') ^ 2 = 4 * u' ^ 2 by ring]
      have h4 : c_loc * (r : ℝ) * θ * (û : ℝ) ^ 2 ≤ 4 * ((r : ℝ) * (c_loc * θ * u' ^ 2)) := by
        have hcrθ : c_loc * (r : ℝ) * θ ≥ 0 := by positivity
        nlinarith only [hcrθ, h3]
      linarith only [h2, h4, mul_le_mul_of_nonneg_left hgap0 hrpos.le]
    calc ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
            (open Classical in if ∃ i, cloudSum σ i = 0 then (1 : ℝ) else 0)
        ≤ ∑ _i : Fin n, Real.exp (-((r : ℝ) * Ftheta S θ u')) :=
            le_trans hstep1 (Finset.sum_le_sum fun i _ => heach i)
      _ = (n : ℝ) * Real.exp (-((r : ℝ) * Ftheta S θ u')) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ Real.exp L * Real.exp (- (2 * L)) := by
            refine mul_le_mul ?_ (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
            exact le_trans hnL (by linarith [Real.add_one_le_exp L])
      _ = Real.exp (-L) := by rw [← Real.exp_add]; congr 1; ring
  have hPart2 :
      (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
          (Real.exp |Dy J₀ h₀ (û : ℝ) y σ| *
            (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0))) ≤ Real.exp (-L) := by
    let W := max 1 (width J₀ h₀)
    let Mtilt : ℝ := L + (Kpow : ℝ) * (n : ℝ) * Real.log ((r : ℝ) + 1) + 1
    let Λ : ℝ := (3 / 2 + 2 * Mtilt) * (n : ℝ) * W ^ 2
    have hMtilt_nn : 0 ≤ Mtilt := by dsimp [Mtilt]; positivity
    have hΛ_nn : 0 ≤ Λ := by dsimp [Λ]; positivity
    have hΛ_le : Λ ≤ (c_loc / 3) * (r : ℝ) * θ * (û : ℝ) ^ 2 := by
      have hM_le : 3 / 2 + 2 * Mtilt ≤ (3 / 2 + 2 * ((Kpow : ℝ) + 2)) * ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1) := by
        have h1 : Mtilt ≤ ((Kpow : ℝ) + 2) * ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1) := by
          dsimp [Mtilt]
          have hKp_nn : (0 : ℝ) ≤ (Kpow : ℝ) := Nat.cast_nonneg _
          nlinarith only [mul_nonneg hnpos.le hlog_nn, hL_ge1, hKp_nn]
        have h2 : 3 / 2 ≤ (3 / 2) * ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1) := by linarith
        linarith
      have hCs3 : 3 * (3 / 2 + 2 * ((Kpow : ℝ) + 2)) / c_loc ≤ Cₛ :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have hCs_mul : 3 * (3 / 2 + 2 * ((Kpow : ℝ) + 2)) ≤ c_loc * Cₛ := by
        have := mul_le_mul_of_nonneg_left hCs3 hc_loc_pos.le
        have heq : c_loc * (3 * (3 / 2 + 2 * ((Kpow : ℝ) + 2)) / c_loc) = 3 * (3 / 2 + 2 * ((Kpow : ℝ) + 2)) := by
          field_simp [hc_loc_pos.ne']
        linarith
      have h3Λ : 3 * Λ ≤ c_loc * ((r : ℝ) * θ * (û : ℝ) ^ 2) := by
        calc 3 * Λ = 3 * (3 / 2 + 2 * Mtilt) * ((n : ℝ) * W ^ 2) := by dsimp [Λ]; ring
          _ ≤ 3 * ((3 / 2 + 2 * ((Kpow : ℝ) + 2)) * ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1)) *
                ((n : ℝ) * W ^ 2) := by
                gcongr
          _ = (3 * (3 / 2 + 2 * ((Kpow : ℝ) + 2))) *
                ((n : ℝ) * W ^ 2 * ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1)) := by ring
          _ ≤ (c_loc * Cₛ) * ((n : ℝ) * W ^ 2 * ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1)) := by
                gcongr
          _ = c_loc * (Cₛ * (n : ℝ) * W ^ 2 * ((n : ℝ) * Real.log ((r : ℝ) + 1) + L + 1)) := by ring
          _ ≤ c_loc * ((r : ℝ) * θ * (û : ℝ) ^ 2) := by
                refine mul_le_mul_of_nonneg_left ?_ hc_loc_pos.le
                exact hcond
      linarith
    have hpt : ∀ σ : Config S (Fin n × Fin r),
        nuProd S (tau S + θ) y σ *
            (Real.exp |Dy J₀ h₀ (û : ℝ) y σ| *
              (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0)) ≤
          nuProd S (tau S + θ) y σ * Real.exp (1 / 4 - Mtilt) *
            ∏ i : Fin n, Real.exp (Λ * (|cloudSum σ i| / ((r : ℝ) * (û : ℝ)) - 1) ^ 2) := by
      intro σ
      by_cases hσ0 : nuProd S (tau S + θ) y σ = 0
      · simp [hσ0]
      · have hsign := nuProd_ne_zero_sign S (tau S + θ) y σ hσ0
        have hDy := dy_abs_bound hn J₀ hSymm h₀ (û : ℝ) hû_pos hrpos y σ hsign
        dsimp at hDy
        have hProd_eq : Real.exp (Λ * ∑ i : Fin n, (|cloudSum σ i| / ((r : ℝ) * (û : ℝ)) - 1) ^ 2) =
            ∏ i : Fin n, Real.exp (Λ * (|cloudSum σ i| / ((r : ℝ) * (û : ℝ)) - 1) ^ 2) := by
          rw [Finset.mul_sum, Real.exp_sum]
        rw [← hProd_eq, mul_assoc (nuProd S (tau S + θ) y σ), ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left ?_ (nuProd_nonneg _ _ _ _)
        by_cases hlt1 : 1 < |Dy J₀ h₀ (û : ℝ) y σ|
        · simp only [hlt1, ↓reduceIte, mul_one, Real.exp_le_exp]
          have hbig : 1 / 2 ≤ (n : ℝ) * W ^ 2 * ∑ i : Fin n, (|cloudSum σ i| / ((r : ℝ) * (û : ℝ)) - 1) ^ 2 := by
            linarith
          have htilted : 0 ≤ Mtilt * (2 * (n : ℝ) * W ^ 2 * ∑ i : Fin n, (|cloudSum σ i| / ((r : ℝ) * (û : ℝ)) - 1) ^ 2 - 1) :=
            mul_nonneg hMtilt_nn (by linarith)
          dsimp [Λ]
          linarith
        · simp only [hlt1, ↓reduceIte, mul_zero]
          exact (Real.exp_pos _).le
    calc ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
            (Real.exp |Dy J₀ h₀ (û : ℝ) y σ| *
              (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0))
        ≤ ∑ σ : Config S (Fin n × Fin r),
            Real.exp (1 / 4 - Mtilt) * (nuProd S (tau S + θ) y σ *
              ∏ i : Fin n, Real.exp (Λ * (|cloudSum σ i| / ((r : ℝ) * (û : ℝ)) - 1) ^ 2)) := by
            refine Finset.sum_le_sum fun σ _ => ?_
            linarith [hpt σ]
      _ = Real.exp (1 / 4 - Mtilt) * ∑ σ : Config S (Fin n × Fin r),
            nuProd S (tau S + θ) y σ *
              ∏ i : Fin n, Real.exp (Λ * (|cloudSum σ i| / ((r : ℝ) * (û : ℝ)) - 1) ^ 2) :=
            (Finset.mul_sum _ _ _).symm
      _ = Real.exp (1 / 4 - Mtilt) * ∏ i : Fin n, ∑ τ : Config S (Fin r),
            nuPm S (tau S + θ) (y i) τ * Real.exp (Λ * (|oneSum τ| / ((r : ℝ) * (û : ℝ)) - 1) ^ 2) := by
            congr 1
            exact nuProd_sum_prod S (tau S + θ) n r y
              (fun _ τ => Real.exp (Λ * (|oneSum τ| / ((r : ℝ) * (û : ℝ)) - 1) ^ 2))
      _ ≤ Real.exp (1 / 4 - Mtilt) * ∏ _i : Fin n, ((r : ℝ) + 1) ^ Kpow := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun τ _ =>
              mul_nonneg (nuPm_nonneg _ _ _ _) (Real.exp_pos _).le) fun i _ => ?_
            exact hexp_cap r θ u' (û : ℝ) Λ (y i) hr hr_big hθ_pos hθ_le hu_fp.1 hu_fp.2.1 hu_fp.2.2
              hgap_u hû_diff hû_lo hû_hi hΛ_nn hΛ_le
      _ = Real.exp (1 / 4 - Mtilt) * Real.exp ((Kpow : ℝ) * (n : ℝ) * Real.log ((r : ℝ) + 1)) := by
            congr 1
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            have hr1_pos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
            calc (((r : ℝ) + 1) ^ Kpow) ^ n = ((r : ℝ) + 1) ^ (Kpow * n) := (pow_mul _ _ _).symm
              _ = ((r : ℝ) + 1) ^ ((Kpow * n : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
              _ = Real.exp (Real.log ((r : ℝ) + 1) * ((Kpow * n : ℕ) : ℝ)) := Real.rpow_def_of_pos hr1_pos _
              _ = Real.exp ((Kpow : ℝ) * (n : ℝ) * Real.log ((r : ℝ) + 1)) := by
                  push_cast; ring_nf
      _ ≤ Real.exp (-L) := by
            rw [← Real.exp_add, Real.exp_le_exp]
            dsimp [Mtilt]
            linarith
  have hsum1 := nuProd_sum_one S (tau S + θ) n r y
  have hPart3 :
      Real.exp (-1) * (1 - Real.exp (-L)) ≤
        ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ * Real.exp (Dy J₀ h₀ (û : ℝ) y σ) := by
    have hP_bad :
        ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
            (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0) ≤ Real.exp (-L) := by
      calc ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0)
          ≤ ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              (Real.exp |Dy J₀ h₀ (û : ℝ) y σ| *
                (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0)) := by
              refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (nuProd_nonneg _ _ _ _)
              split_ifs
              · exact (Real.one_le_exp (abs_nonneg _)).trans_eq (mul_one _).symm
              · simp
        _ ≤ Real.exp (-L) := hPart2
    have hlow : ∀ σ : Config S (Fin n × Fin r),
        Real.exp (-1) * (1 - (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0)) ≤
          Real.exp (Dy J₀ h₀ (û : ℝ) y σ) := by
      intro σ
      by_cases hgt : 1 < |Dy J₀ h₀ (û : ℝ) y σ|
      · simp only [hgt, ↓reduceIte, sub_self, mul_zero]
        exact (Real.exp_pos _).le
      · simp only [hgt, ↓reduceIte, sub_zero, mul_one, Real.exp_le_exp]
        linarith [(abs_le.mp (not_lt.mp hgt)).1]
    calc Real.exp (-1) * (1 - Real.exp (-L))
        ≤ Real.exp (-1) * (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
            (1 - (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0))) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            have heq : ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
                  (1 - (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0)) =
                1 - ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
                  (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0) := by
              simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, hsum1]
            linarith
      _ = ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
            (Real.exp (-1) * (1 - (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun σ _ => by ring
      _ ≤ ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ * Real.exp (Dy J₀ h₀ (û : ℝ) y σ) :=
            Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hlow σ) (nuProd_nonneg _ _ _ _)
  have hPart4 :
      ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ * Real.exp (Dy J₀ h₀ (û : ℝ) y σ) ≤
        Real.exp 1 + Real.exp (-L) := by
    have hpt : ∀ σ : Config S (Fin n × Fin r),
        Real.exp (Dy J₀ h₀ (û : ℝ) y σ) ≤
          Real.exp 1 + Real.exp |Dy J₀ h₀ (û : ℝ) y σ| *
            (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0) := by
      intro σ
      by_cases hgt : 1 < |Dy J₀ h₀ (û : ℝ) y σ|
      · simp only [hgt, ↓reduceIte, mul_one]
        have : Real.exp (Dy J₀ h₀ (û : ℝ) y σ) ≤ Real.exp |Dy J₀ h₀ (û : ℝ) y σ| :=
          Real.exp_le_exp.mpr (le_abs_self _)
        linarith [Real.exp_pos (1 : ℝ)]
      · simp only [hgt, ↓reduceIte, mul_zero, add_zero, Real.exp_le_exp]
        exact (abs_le.mp (not_lt.mp hgt)).2
    calc ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ * Real.exp (Dy J₀ h₀ (û : ℝ) y σ)
        ≤ ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
            (Real.exp 1 + Real.exp |Dy J₀ h₀ (û : ℝ) y σ| *
              (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0)) :=
            Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hpt σ) (nuProd_nonneg _ _ _ _)
      _ = Real.exp 1 * (∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ) +
            ∑ σ : Config S (Fin n × Fin r), nuProd S (tau S + θ) y σ *
              (Real.exp |Dy J₀ h₀ (û : ℝ) y σ| *
                (if 1 < |Dy J₀ h₀ (û : ℝ) y σ| then (1 : ℝ) else 0)) := by
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
            congr 1; ring
      _ ≤ Real.exp 1 + Real.exp (-L) := by
            rw [hsum1, mul_one]
            linarith [hPart2]
  exact ⟨hPart1, hPart2, hPart3, hPart4⟩


