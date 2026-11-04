-- Prove2me | solution 1 for CappedBaseStock.main
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:07:44.42313+00:00
-- url     : https://prove2.me/submissions/fe39b739-57cf-44b0-9455-04fc9303b8cd

import Theorems.Thm_CappedBaseStock_lower_certificate_bound
import Theorems.Thm_CappedBaseStock_finite_cap_cost_bound
import Theorems.Thm_CappedBaseStock_base_stock_cost_bound
import Theorems.Thm_CappedBaseStock_two_branch

/-! Main theorem reduction to the four published manuscript milestones.
The solution has the target's exact hypotheses. The auxiliary scalar conversion,
policy-infimum comparison, and final constant bound are proved here. -/

open scoped ENNReal NNReal
open CappedBaseStock

namespace CappedBaseStockMainProof

lemma kappa_pos (c : Parameters) : 0 < kappa c.L := by
  have hL : (1 : ℝ) ≤ c.L := by exact_mod_cast c.leadTime_pos
  have hden : 0 < 3 * (c.L : ℝ) - 1 := by linarith
  unfold kappa
  positivity

lemma kappa_le_seven_thirds (c : Parameters) : kappa c.L ≤ (7 / 3 : ℝ) := by
  have hL : (1 : ℝ) ≤ c.L := by exact_mod_cast c.leadTime_pos
  have hden : 0 < ((c.L : ℝ) + 1) * (3 * (c.L : ℝ) - 1) := by
    have : 0 < 3 * (c.L : ℝ) - 1 := by linarith
    positivity
  have hfrac : 4 * (c.L : ℝ) ^ 2 /
      (((c.L : ℝ) + 1) * (3 * (c.L : ℝ) - 1)) ≤ (4 / 3 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  unfold kappa
  linarith

lemma combined_real_bound (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    min
      ((c.h + c.p / ((c.L : ℝ) + 1)) * z +
        (2 - 1 / ((c.L : ℝ) + 1)) * c.p * (mean P - r))
      (2 * c.h * z +
        ((2 - 1 / ((c.L : ℝ) + 1)) * c.p + c.h * (c.L : ℝ)) * (mean P - r)) ≤
      kappa c.L * (c.h * z + c.p * (mean P - r)) := by
  have hLp : 0 < (c.L : ℝ) + 1 := by positivity
  have hlambda : 0 < c.h * ((c.L : ℝ) + 1) / c.p :=
    div_pos (mul_pos c.holding_pos hLp) c.penalty_pos
  have hCh : 0 ≤ c.h * z := mul_nonneg (le_of_lt c.holding_pos) feasible.2.2.1
  have hCp : 0 ≤ c.p * (mean P - r) :=
    mul_nonneg (le_of_lt c.penalty_pos) (sub_nonneg.mpr feasible.2.1)
  have hbranch := two_branch c.L c.leadTime_pos
    (c.h * ((c.L : ℝ) + 1) / c.p) (c.h * z) (c.p * (mean P - r)) hlambda hCh hCp
  have hA :
      (c.h + c.p / ((c.L : ℝ) + 1)) * z +
          (2 - 1 / ((c.L : ℝ) + 1)) * c.p * (mean P - r) =
        (1 + 1 / (c.h * ((c.L : ℝ) + 1) / c.p)) * (c.h * z) +
          (1 + (c.L : ℝ) / ((c.L : ℝ) + 1)) * (c.p * (mean P - r)) := by
    field_simp [ne_of_gt c.holding_pos, ne_of_gt c.penalty_pos, ne_of_gt hLp]
    ring
  have hB :
      2 * c.h * z +
          ((2 - 1 / ((c.L : ℝ) + 1)) * c.p + c.h * (c.L : ℝ)) * (mean P - r) =
        2 * (c.h * z) +
          (1 + (c.L : ℝ) / ((c.L : ℝ) + 1) +
            (c.h * ((c.L : ℝ) + 1) / c.p) * ((c.L : ℝ) / ((c.L : ℝ) + 1))) *
            (c.p * (mean P - r)) := by
    field_simp [ne_of_gt c.penalty_pos, ne_of_gt hLp]
    ring
  simpa only [← hA, ← hB, kappa] using hbranch

end CappedBaseStockMainProof

namespace CappedBaseStockMainProof

lemma cbsOpt_le_cbsCost (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) :
    CbsOpt P c ≤ cbsCost P c S r := by
  exact iInf_le_of_le S (iInf_le_of_le r le_rfl)

lemma cbsOpt_le_scaled_objective (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z)
    (hk : 0 ≤ kappa c.L)
    (hscalar : min
      ((c.h + c.p / ((c.L : ℝ) + 1)) * z +
        (2 - 1 / ((c.L : ℝ) + 1)) * c.p * (mean P - r))
      (2 * c.h * z +
        ((2 - 1 / ((c.L : ℝ) + 1)) * c.p + c.h * (c.L : ℝ)) * (mean P - r)) ≤
      kappa c.L * (c.h * z + c.p * (mean P - r))) :
    CbsOpt P c ≤ ENNReal.ofReal (kappa c.L) * certificateObjective P c r z := by
  have hcap := (cbsOpt_le_cbsCost P c _ _).trans
    (finite_cap_cost_bound P c r z feasible)
  have hbase := (cbsOpt_le_cbsCost P c _ _).trans
    (base_stock_cost_bound P c r z feasible)
  calc
    CbsOpt P c ≤ min
        (ENNReal.ofReal ((c.h + c.p / ((c.L : ℝ) + 1)) * z +
          (2 - 1 / ((c.L : ℝ) + 1)) * c.p * (mean P - r)))
        (ENNReal.ofReal (2 * c.h * z +
          ((2 - 1 / ((c.L : ℝ) + 1)) * c.p + c.h * (c.L : ℝ)) * (mean P - r))) :=
      le_min hcap hbase
    _ ≤ ENNReal.ofReal (kappa c.L * (c.h * z + c.p * (mean P - r))) := by
      rw [← ENNReal.ofReal_min]
      exact ENNReal.ofReal_le_ofReal hscalar
    _ = ENNReal.ofReal (kappa c.L) * certificateObjective P c r z := by
      rw [ENNReal.ofReal_mul hk]
      rfl

lemma assemble (P : DemandLaw) (c : Parameters)
    (hk : 0 < kappa c.L)
    (hkupper : kappa c.L ≤ (7 / 3 : ℝ))
    (hpoint : ∀ r z : ℝ, CertificateFeasible P c r z →
      CbsOpt P c ≤ ENNReal.ofReal (kappa c.L) * certificateObjective P c r z) :
    CbsOpt P c ≤ ENNReal.ofReal (kappa c.L) * lowerCertificate P c ∧
    CbsOpt P c ≤ ENNReal.ofReal (kappa c.L) * OPT P c ∧
    ENNReal.ofReal (kappa c.L) * OPT P c ≤ (7 / 3 : ℝ≥0∞) * OPT P c := by
  have hcert : CbsOpt P c ≤ ENNReal.ofReal (kappa c.L) * lowerCertificate P c := by
    unfold lowerCertificate
    rw [ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hk))
      ENNReal.ofReal_ne_top]
    exact le_iInf fun rz => hpoint rz.val.1 rz.val.2 rz.property
  refine ⟨hcert, hcert.trans (mul_le_mul_right (lower_certificate_bound P c) _), ?_⟩
  apply mul_le_mul_left
  calc
    ENNReal.ofReal (kappa c.L) ≤ ENNReal.ofReal (7 / 3 : ℝ) :=
      ENNReal.ofReal_le_ofReal hkupper
    _ = (7 / 3 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num

end CappedBaseStockMainProof

/-- The complete target statement, conditional only on the imported milestones. -/
theorem solution (P : DemandLaw) (c : Parameters) :
    CbsOpt P c ≤ ENNReal.ofReal (kappa c.L) * lowerCertificate P c ∧
    CbsOpt P c ≤ ENNReal.ofReal (kappa c.L) * OPT P c ∧
    ENNReal.ofReal (kappa c.L) * OPT P c ≤ (7 / 3 : ℝ≥0∞) * OPT P c := by
  apply CappedBaseStockMainProof.assemble P c
    (CappedBaseStockMainProof.kappa_pos c)
    (CappedBaseStockMainProof.kappa_le_seven_thirds c)
  intro r z feasible
  exact CappedBaseStockMainProof.cbsOpt_le_scaled_objective P c r z feasible
    (CappedBaseStockMainProof.kappa_pos c).le
    (CappedBaseStockMainProof.combined_real_bound P c r z feasible)
