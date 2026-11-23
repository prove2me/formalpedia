-- Prove2me | solution 1 for Experiments.eq_exp_of_sequence_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:06.634774+00:00
-- url     : https://prove2.me/submissions/e372f95d-81ee-46c7-aab9-4e3de90944fc

import Definitions.Def_Experiments_GeneratorBound
import Definitions.Def_Experiments_FiniteDifferenceSemigroup
import Theorems.Thm_Experiments_constant_of_sequence_slopes

set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
namespace Experiments
theorem _root_.solution (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    (a : A) (h : ℕ → ℝ) (hpos : ∀ n, 0 < h n)
    (hz : Tendsto h atTop (𝓝 0))
    (ha : Tendsto (fun n => (h n)⁻¹ • (M (h n) - 1)) atTop (𝓝 a)) :
    ∀ t, 0 ≤ t → M t = exp (t • a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  intro t ht
  let F : ℝ → A := fun x => M x * exp (x • -a)
  have hFc : ContinuousOn F (Icc 0 t) := fun x hx =>
    ((hcont x hx.1).mono Icc_subset_Ici_self).mul
      (hasDerivAt_exp_smul_const (-a) x).continuousAt.continuousWithinAt
  have hFq : ∀ x ∈ Ico 0 t,
      Tendsto (fun n => (h n)⁻¹ • (F (x + h n) - F x)) atTop (𝓝 0) := by
    intro x hx
    have hright : Tendsto h atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hz, Eventually.of_forall hpos⟩
    have hec : Tendsto (fun n => exp ((x + h n) • -a)) atTop (𝓝 (exp (x • -a))) :=
      (hasDerivAt_exp_smul_const (-a) x).continuousAt.tendsto.comp
        (by simpa using tendsto_const_nhds.add hz)
    have hed := (hasDerivAt_exp_smul_const' (-a) x).tendsto_slope_zero_right.comp hright
    have hlim := (tendsto_const_nhds (x := M x)).mul ((ha.mul hec).add hed)
    have hlim' : Tendsto
        (fun n => M x * (((h n)⁻¹ • (M (h n) - 1)) * exp ((x + h n) • -a) +
          (h n)⁻¹ • (exp ((x + h n) • -a) - exp (x • -a))))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_mul, add_neg_cancel, mul_zero] using hlim
    apply hlim'.congr'
    apply Eventually.of_forall
    intro n
    dsimp [F]
    rw [hadd x (h n) hx.1 (hpos n).le]
    simp only [smul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_add, mul_sub, mul_assoc]
    abel
  have hFt : F t = 1 := by
    rw [constant_of_sequence_slopes hpos hz ht hFc hFq]
    simp [F, h0]
  have hinv : exp (t • -a) * exp (t • a) = 1 := by
    rw [← exp_add_of_commute (((Commute.refl a).neg_left.smul_left t).smul_right t),
      smul_neg, neg_add_cancel, exp_zero]
  calc
    M t = M t * (exp (t • -a) * exp (t • a)) := by rw [hinv, mul_one]
    _ = F t * exp (t • a) := by rw [← mul_assoc]
    _ = exp (t • a) := by rw [hFt, one_mul]
end Experiments
