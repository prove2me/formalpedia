-- Prove2me | solution 1 for DynkinAsymInfo.Linear.lemma_6_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:50:36.320641+00:00
-- url     : https://prove2.me/submissions/f9ef9cf2-6c05-42b2-acfc-616ec0a0945a

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_ClosedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear.L69

open DynkinAsymInfo.Linear

lemma omega_pos (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : 0 < signalNoise p := by
  unfold signalNoise
  exact div_pos (by linarith) p.sigma_pos

lemma sigma_omega (p : Params) : p.sigma * signalNoise p = p.mu1 - p.mu0 := by
  unfold signalNoise
  field_simp [p.sigma_pos.ne']

lemma quadA_pos (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : 0 < quadA p := by
  unfold quadA
  have := omega_pos p h62
  positivity

lemma discr_gt (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : quadB p ^ 2 < discr p := by
  unfold discr
  have := quadA_pos p h62
  nlinarith [h62.1]

lemma abs_lt_sqrt (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) :
    |quadB p| < Real.sqrt (discr p) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (discr_gt p h62)

lemma beta1_pos (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : 0 < beta1 p := by
  unfold beta1
  have h1 := abs_lt_sqrt p h62
  have h2 := quadA_pos p h62
  have h3 := neg_abs_le (quadB p)
  have h4 := le_abs_self (quadB p)
  apply div_pos _ (by linarith)
  linarith

lemma beta1_lt_one (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : beta1 p < 1 := by
  unfold beta1
  have h2 := quadA_pos p h62
  have hs : 0 < 2 * quadA p + quadB p := by
    unfold quadA quadB
    have := omega_pos p h62
    have := p.sigma_pos
    have : 0 < p.sigma * signalNoise p := by positivity
    nlinarith
  have hD : discr p < (2 * quadA p + quadB p) ^ 2 := by
    have hsum : quadA p + quadB p + p.mu0 = p.mu1 := by
      unfold quadA quadB; have := sigma_omega p; linarith
    unfold discr
    nlinarith [h62.2]
  have hsq : Real.sqrt (discr p) < 2 * quadA p + quadB p := by
    rw [Real.sqrt_lt' hs]; exact hD
  rw [div_lt_one (by linarith)]
  linarith

lemma beta2_neg (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : beta2 p < 0 := by
  unfold beta2
  have h1 := abs_lt_sqrt p h62
  have h2 := quadA_pos p h62
  have h3 := neg_abs_le (quadB p)
  apply div_neg_of_neg_of_pos _ (by linarith)
  linarith

/-- the derivative of `rootEq` -/
lemma hasDerivAt_rootEq (p : Params) (eps z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun z => rootEq p eps z)
      ((1 - beta2 p) * ((beta1 p - 1) * z ^ (beta1 p - 1 - 1)) +
        (beta1 p - 1) * ((beta2 p - 1) * z ^ (beta2 p - 1 - 1))) z := by
  unfold rootEq
  have h1 := Real.hasDerivAt_rpow_const (x := z) (p := beta1 p - 1) (Or.inl hz.ne')
  have h2 := Real.hasDerivAt_rpow_const (x := z) (p := beta2 p - 1) (Or.inl hz.ne')
  have := ((h1.const_mul (1 - beta2 p)).add (h2.const_mul (beta1 p - 1))).sub_const
    ((beta1 p - beta2 p) / (1 + eps))
  exact this

lemma rootEq_strictMonoOn (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) (eps : ℝ) :
    StrictMonoOn (fun z => rootEq p eps z) (Set.Ioc 0 1) := by
  have hb1 := beta1_lt_one p h62
  have hb1p := beta1_pos p h62
  have hb2 := beta2_neg p h62
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 1)
  · intro z hz
    exact (hasDerivAt_rootEq p eps z hz.1).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioc] at hz
    rw [(hasDerivAt_rootEq p eps z hz.1).deriv]
    have hlt : z ^ (beta1 p - 1 - 1) < z ^ (beta2 p - 1 - 1) :=
      Real.rpow_lt_rpow_of_exponent_gt hz.1 hz.2 (by linarith)
    have hneg : (1 - beta2 p) * (beta1 p - 1) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have : (1 - beta2 p) * ((beta1 p - 1) * z ^ (beta1 p - 1 - 1)) +
        (beta1 p - 1) * ((beta2 p - 1) * z ^ (beta2 p - 1 - 1)) =
        ((1 - beta2 p) * (beta1 p - 1)) * (z ^ (beta1 p - 1 - 1) - z ^ (beta2 p - 1 - 1)) := by
      ring
    rw [this]
    exact mul_pos_of_neg_of_neg hneg (by linarith)

lemma rootEq_one (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) (eps : ℝ) (heps : 0 < eps) :
    0 < rootEq p eps 1 := by
  unfold rootEq
  simp only [Real.one_rpow]
  have hb1 := beta1_pos p h62
  have hb2 := beta2_neg p h62
  have hd : 0 < beta1 p - beta2 p := by linarith
  have : (beta1 p - beta2 p) / (1 + eps) < beta1 p - beta2 p := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  linarith

lemma exists_neg (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) (eps : ℝ) (heps : 0 < eps) :
    ∃ z ∈ Set.Ioo (0 : ℝ) 1, rootEq p eps z < 0 := by
  have hb1 := beta1_pos p h62
  have hb1' := beta1_lt_one p h62
  have hb2 := beta2_neg p h62
  set e := beta1 p - beta2 p with he
  have hepos : 0 < e := by linarith
  set c := (1 - beta1 p) / (2 * (1 - beta2 p)) with hc
  have hcpos : 0 < c := div_pos (by linarith) (by linarith)
  have hclt : c < 1 := by rw [div_lt_one (by linarith)]; linarith
  refine ⟨c ^ e⁻¹, ⟨Real.rpow_pos_of_pos hcpos _, ?_⟩, ?_⟩
  · exact Real.rpow_lt_one hcpos.le hclt (inv_pos.mpr hepos)
  · set z := c ^ e⁻¹ with hz
    have hzpos : 0 < z := Real.rpow_pos_of_pos hcpos _
    have hze : z ^ e = c := Real.rpow_inv_rpow hcpos.le hepos.ne'
    have hsplit : z ^ (beta1 p - 1) = z ^ e * z ^ (beta2 p - 1) := by
      rw [← Real.rpow_add hzpos]; congr 1; rw [he]; ring
    unfold rootEq
    rw [hsplit, hze]
    have hzq : 0 < z ^ (beta2 p - 1) := Real.rpow_pos_of_pos hzpos _
    have hcc : (1 - beta2 p) * c = (1 - beta1 p) / 2 := by
      have : (1 - beta2 p) ≠ 0 := by linarith
      rw [hc]; field_simp
    have hdiv : 0 < (beta1 p - beta2 p) / (1 + eps) := div_pos (by linarith) (by linarith)
    have : (1 - beta2 p) * (c * z ^ (beta2 p - 1)) + (beta1 p - 1) * z ^ (beta2 p - 1) =
        ((1 - beta2 p) * c + (beta1 p - 1)) * z ^ (beta2 p - 1) := by ring
    rw [this, hcc]
    have : ((1 - beta1 p) / 2 + (beta1 p - 1)) * z ^ (beta2 p - 1) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hzq
    linarith

end DynkinAsymInfo.Linear.L69

open DynkinAsymInfo.Linear in
theorem solution (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) :
    beta1 p ∈ Set.Ioo 0 1 ∧ beta2 p < 0 ∧
      ∃! z : ℝ, z ∈ Set.Ioo 0 1 ∧ rootEq p eps z = 0 := by
  refine ⟨⟨L69.beta1_pos p h62, L69.beta1_lt_one p h62⟩, L69.beta2_neg p h62, ?_⟩
  obtain ⟨z0, hz0, hneg⟩ := L69.exists_neg p h62 eps heps
  have hcont : ContinuousOn (fun z => rootEq p eps z) (Set.Icc z0 1) := by
    intro z hz
    exact (L69.hasDerivAt_rootEq p eps z (lt_of_lt_of_le hz0.1 hz.1)).continuousAt.continuousWithinAt
  have hmem : (0 : ℝ) ∈ Set.Icc (rootEq p eps z0) (rootEq p eps 1) :=
    ⟨hneg.le, (L69.rootEq_one p h62 eps heps).le⟩
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hz0.2.le hcont hmem
  have hr1 : r ≠ 1 := by
    rintro rfl; have := L69.rootEq_one p h62 eps heps; simp only at hr0; linarith
  refine ⟨r, ⟨⟨lt_of_lt_of_le hz0.1 hr.1, lt_of_le_of_ne hr.2 hr1⟩, hr0⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  have hmono := L69.rootEq_strictMonoOn p h62 eps
  have hrI : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_lt_of_le hz0.1 hr.1, hr.2⟩
  have hyI : y ∈ Set.Ioc (0 : ℝ) 1 := ⟨hy.1, hy.2.le⟩
  exact hmono.injOn hyI hrI (by simp only at hr0 ⊢; rw [hy0, hr0])
