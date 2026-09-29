-- Prove2me | solution 1 for BookProof.ScalaronEdge.edge_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T13:56:34.153681+00:00
-- url     : https://prove2.me/submissions/5ec4585b-81c1-41e4-b6f5-40a907461f8f

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.edge_energy_bound
import Mathlib
import Definitions.Def_ChapterScalaronEdge
import Theorems.Thm_BookProof_ScalaronEdge_edgeKinConst_pos
import Theorems.Thm_BookProof_ScalaronEdge_edgeMassConst_pos
import Theorems.Thm_BookProof_ScalaronEdge_edge_sup_sq_le
open BookProof.ScalaronEdge










open Complex Real MeasureTheory Function SchwartzMap ComplexOrder
open BookProof.Starobinsky
open BookProof.ScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.FarisLavine
open BookProof.WallEsaSemibounded
open BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert



variable (M alpha : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution {A B c : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    (V : ℝ → ℝ) (hVcont : Continuous V) (hVnn : ∀ x, 0 ≤ V x)
    (hVout : ∀ x, x ∉ Set.Icc (-A) B → c ≤ V x)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    min (edgeKinConst A B) (edgeMassConst c) * (∫ x, ‖f x‖ ^ 2)
      ≤ (∫ x, ‖deriv f x‖ ^ 2) + ∫ x, V x * ‖f x‖ ^ 2 := by

  have hL : 0 < A + B := by linarith
  set S := ∫ x, ‖f x‖ ^ 2 with hS
  set T := ∫ x, ‖deriv f x‖ ^ 2 with hT
  set U := ∫ x, V x * ‖f x‖ ^ 2 with hU
  have hcont0 : Continuous f := hf.continuous
  have hcont1 : Continuous (deriv f) := (hf.deriv' (n := 1)).continuous
  have hs1 : HasCompactSupport (deriv f) := hs.deriv
  have hsq : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
  have hsqsupp : HasCompactSupport fun x => ‖f x‖ ^ 2 :=
    hs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hSint : Integrable fun x => ‖f x‖ ^ 2 := hsq.integrable_of_hasCompactSupport hsqsupp
  have hTint : Integrable fun x => ‖deriv f x‖ ^ 2 :=
    (by fun_prop : Continuous fun x => ‖deriv f x‖ ^ 2).integrable_of_hasCompactSupport
      (hs1.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
  have hUint : Integrable fun x => V x * ‖f x‖ ^ 2 :=
    (hVcont.mul hsq).integrable_of_hasCompactSupport hsqsupp.mul_left
  have hSnn : 0 ≤ S := integral_nonneg fun x => by positivity
  have hTnn : 0 ≤ T := integral_nonneg fun x => by positivity
  have hUnn : 0 ≤ U := integral_nonneg fun x => by have := hVnn x; positivity
  have hsplit : (∫ t, ((2 * (A + B))⁻¹ * ‖f t‖ ^ 2 + (2 * (A + B)) * ‖deriv f t‖ ^ 2))
      = (2 * (A + B))⁻¹ * S + (2 * (A + B)) * T := by
    rw [integral_add (hSint.const_mul _) (hTint.const_mul _), integral_const_mul,
      integral_const_mul]
  have hsup : ∀ x, ‖f x‖ ^ 2 ≤ (2 * (A + B))⁻¹ * S + (2 * (A + B)) * T := by
    intro x
    have hδ : (0 : ℝ) < (2 * (A + B))⁻¹ := by positivity
    have := edge_sup_sq_le f hf hs hδ x
    rw [inv_inv] at this
    rw [← hsplit]
    exact this
  have hmeas : volume (Set.Icc (-A) B) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hvol : volume.real (Set.Icc (-A) B) = A + B := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
  have hin : ∫ x in Set.Icc (-A) B, ‖f x‖ ^ 2
      ≤ (A + B) * ((2 * (A + B))⁻¹ * S + (2 * (A + B)) * T) := by
    have h1 : ∫ x in Set.Icc (-A) B, ‖f x‖ ^ 2
        ≤ ∫ _x in Set.Icc (-A) B, ((2 * (A + B))⁻¹ * S + (2 * (A + B)) * T) :=
      setIntegral_mono_on hSint.integrableOn (integrableOn_const hmeas)
        measurableSet_Icc (fun x _ => hsup x)
    rw [setIntegral_const, hvol, smul_eq_mul] at h1
    exact h1
  have hout : ∫ x in (Set.Icc (-A) B)ᶜ, ‖f x‖ ^ 2 ≤ U / c := by
    have h1 : ∫ x in (Set.Icc (-A) B)ᶜ, ‖f x‖ ^ 2
        ≤ ∫ x in (Set.Icc (-A) B)ᶜ, V x * ‖f x‖ ^ 2 / c := by
      refine setIntegral_mono_on hSint.integrableOn (hUint.div_const c).integrableOn
        measurableSet_Icc.compl (fun x hx => ?_)
      have hVx := hVout x hx
      rw [le_div_iff₀ hc]
      nlinarith [sq_nonneg ‖f x‖]
    have h2 : ∫ x in (Set.Icc (-A) B)ᶜ, V x * ‖f x‖ ^ 2 / c ≤ ∫ x, V x * ‖f x‖ ^ 2 / c :=
      setIntegral_le_integral (hUint.div_const c)
        (Filter.Eventually.of_forall fun x => by have := hVnn x; positivity)
    have h3 : (∫ x, V x * ‖f x‖ ^ 2 / c) = U / c := integral_div c _
    linarith
  have hSsplit : (∫ x in Set.Icc (-A) B, ‖f x‖ ^ 2)
      + ∫ x in (Set.Icc (-A) B)ᶜ, ‖f x‖ ^ 2 = S := integral_add_compl measurableSet_Icc hSint
  have hkey : S ≤ (A + B) * ((2 * (A + B))⁻¹ * S + (2 * (A + B)) * T) + U / c := by linarith
  have hkey2 : S ≤ 4 * (A + B) ^ 2 * T + 2 * (U / c) := by
    have hexp : (A + B) * ((2 * (A + B))⁻¹ * S + (2 * (A + B)) * T)
        = S / 2 + 2 * (A + B) ^ 2 * T := by field_simp
    rw [hexp] at hkey
    linarith
  set m := min (edgeKinConst A B) (edgeMassConst c) with hm
  have hm1 : m ≤ 1 / (4 * (A + B) ^ 2) := min_le_left _ _
  have hm2 : m ≤ c / 2 := min_le_right _ _
  have hmpos : 0 < m := lt_min (edgeKinConst_pos hA hB) (edgeMassConst_pos hc)
  have h4L : (0 : ℝ) < 4 * (A + B) ^ 2 := by positivity
  have hm1' : m * (4 * (A + B) ^ 2) ≤ 1 := by rw [le_div_iff₀ h4L] at hm1; exact hm1
  calc m * S ≤ m * (4 * (A + B) ^ 2 * T + 2 * (U / c)) := by nlinarith
    _ ≤ T + U := by
        have hA1 : m * (4 * (A + B) ^ 2 * T) ≤ T := by nlinarith
        have hA2 : m * (2 * (U / c)) ≤ U := by
          have hUc : 0 ≤ U / c := by positivity
          have hmc : m * 2 ≤ c := by linarith
          calc m * (2 * (U / c)) = (m * 2) * (U / c) := by ring
            _ ≤ c * (U / c) := mul_le_mul_of_nonneg_right hmc hUc
            _ = U := by field_simp
        linarith
