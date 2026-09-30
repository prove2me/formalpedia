-- Prove2me | solution 1 for ChitourPrescribedTime.Linear.transformed_dynamics
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:43:20.978739+00:00
-- url     : https://prove2.me/submissions/7521afd0-1b84-458f-abac-6b821ead218d

import Definitions.Def_ChitourPrescribedTime_Linear_timeChange
import Definitions.Def_ChitourPrescribedTime_Linear_chain
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic
open ChitourPrescribedTime.Linear
open MeasureTheory Filter Matrix
open scoped Topology BigOperators

private theorem tail_deriv (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fun u => ∫ v in u..T, a v) (-a t) (Set.Icc 0 T) t := by
  haveI : Fact (t ∈ Set.Icc 0 T) := ⟨ht⟩
  apply intervalIntegral.integral_hasDerivWithinAt_left
  · exact (ha.continuousOn.mono (Set.Icc_subset_Icc ht.1 le_rfl)).intervalIntegrable_of_Icc ht.2
  · exact ha.continuousOn.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
  · exact ha.continuousOn t ht

private theorem lam_deriv (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a)
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) :
    HasDerivWithinAt (lam T a) (a t * lam T a t ^ 2) (Set.Ico 0 T) t := by
  have hd := (tail_deriv T a ha t ⟨ht.1,ht.2.le⟩).inv (ne_of_gt (ha.tail_pos t ht))
  unfold lam
  simp only [one_div]
  convert! hd.mono Set.Ico_subset_Icc_self using 1 <;> simp [div_eq_mul_inv] <;> ring

private theorem dilation_jordan (n : ℕ) (L : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    L^(n-i.val) * (jordanBlock n *ᵥ v) i = L * (jordanBlock n *ᵥ (dil n L *ᵥ v)) i := by
  classical
  have hdil : dil n L *ᵥ v = fun j => L^(n-j.val)*v j := by
    funext j
    exact Matrix.mulVec_diagonal _ _ _
  rw [hdil]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [jordanBlock,Matrix.of_apply]
  by_cases he : j.val=i.val+1
  · have hex : n-i.val=(n-j.val)+1 := by have := j.isLt; omega
    simp only [he,if_true,one_mul,hex,pow_succ]
    ring
  · simp [he]

private theorem dilation_input (n : ℕ) (L : ℝ) (i : Fin n) :
    L^(n-i.val)*eN n i = L*eN n i := by
  simp only [eN]
  by_cases hi : i.val+1=n
  · have h : n-i.val=1 := by omega
    simp [hi,h]
  · simp [hi]

theorem solution (n : ℕ) (T : ℝ) (a b d u : ℝ → ℝ) (x : ℝ → Fin n → ℝ)
    (ha : AdmissibleWeight T a) (t : ℝ) (ht : t ∈ Set.Ioo 0 T)
    (hx : HasDerivAt x (jordanBlock n *ᵥ x t + (d t + b t * u t) • eN n) t) :
    HasDerivAt (fun τ => dil n (lam T a τ) *ᵥ x τ)
      (lam T a t • ((a t • Dr n + jordanBlock n) *ᵥ (dil n (lam T a t) *ᵥ x t) +
        (b t * u t + d t) • eN n)) t := by
  have hl : HasDerivAt (lam T a) (a t * lam T a t ^ 2) t :=
    (lam_deriv T a ha t ⟨ht.1.le,ht.2⟩).hasDerivAt (Ico_mem_nhds ht.1 ht.2)
  apply hasDerivAt_pi.mpr
  intro i
  have hxi := hasDerivAt_pi.mp hx i
  have hd := (hl.pow (n-i.val)).mul hxi
  simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hd
  simp only [dil,Matrix.mulVec_diagonal,Pi.mul_apply]
  convert! hd using 1
  · simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Matrix.add_mulVec,Matrix.smul_mulVec,
      dil,Dr,Matrix.mulVec_diagonal,Pi.mul_apply]
    have hi : n-i.val=(n-i.val-1)+1 := by have := i.isLt; omega
    have hJ := dilation_jordan n (lam T a t) (x t) i
    have hE := dilation_input n (lam T a t) i
    simp only [dil] at hJ

    have hpow : (lam T a t)^(n-i.val) = (lam T a t)^(n-i.val-1) * lam T a t := by
      conv_lhs => rw [hi,pow_succ]
    rw [hpow] at hJ hE ⊢
    nlinarith [congrArg (fun z => (d t+b t*u t)*z) hE]

