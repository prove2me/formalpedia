-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MajorantIntegrals.majIntegral_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:35.449102+00:00
-- url     : https://prove2.me/submissions/50f8cf10-c4af-4947-8e8b-d9e882a58e6f

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Theorems.Thm_Formalism_FourierDecayAlt_P_MajorantIntegrals_radial_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_MajorantIntegrals_volC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MajorantIntegrals
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.MajorantIntegrals
theorem _root_.solution : MajIntegral := by
  intro K x hK hx
  have hK' : (2 : ℝ) < K := by exact_mod_cast hK
  have hcongr : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y)
      (fun y => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioi 0) :=
    fun y hy => radial_eq K x hx y hy
  have hIoc : IntegrableOn (fun y : ℝ => y) (Ioc 0 x) :=
    (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hIoi : IntegrableOn (fun y : ℝ => x ^ K * y ^ ((1 : ℝ) - K)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx).const_mul _
  have hA : IntegrableOn (fun y : ℝ => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioc 0 x) :=
    hIoc.congr_fun (fun y hy => by simp [hy.2]) measurableSet_Ioc
  have hB : IntegrableOn (fun y : ℝ => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioi x) :=
    hIoi.congr_fun (fun y hy => by simp [not_le.mpr (mem_Ioi.mp hy)]) measurableSet_Ioi
  have hint : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y) (Ioi 0) := by
    refine IntegrableOn.congr_fun ?_ hcongr.symm measurableSet_Ioi
    rw [← Ioc_union_Ioi_eq_Ioi hx.le]
    exact hA.union hB
  refine ⟨(integrable_fun_norm_addHaar volume (f := mfac K x)).mpr hint, ?_⟩
  rw [integral_fun_norm_addHaar volume (mfac K x), setIntegral_congr_fun measurableSet_Ioi hcongr,
    ← Ioc_union_Ioi_eq_Ioi hx.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hA hB,
    setIntegral_congr_fun measurableSet_Ioc (fun y hy => if_pos hy.2),
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => if_neg (not_le.mpr (mem_Ioi.mp hy))),
    ← intervalIntegral.integral_of_le hx.le, integral_id, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) hx, volC, Complex.finrank_real_complex]
  have e : x ^ K * x ^ ((1 : ℝ) - K + 1) = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]
    rw [show (K : ℝ) + (1 - K + 1) = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hK2 : (K : ℝ) - 2 ≠ 0 := by linarith
  have hK3 : (1 : ℝ) - K + 1 ≠ 0 := by linarith
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  rw [neg_div, mul_neg, ← mul_div_assoc, e]
  have hK4 : (1 : ℝ) - K + 1 = -((K : ℝ) - 2) := by ring
  rw [hK4]
  field_simp
  ring
end Formalism.FourierDecayAlt.P.MajorantIntegrals
