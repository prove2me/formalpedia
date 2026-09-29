-- Prove2me | solution 1 for AutomorphicForm.table_axis_mem_setOf_xiBox_of_isUnitaryChar_of_mul_mul_rpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/39a4147f-400a-5992-b25f-9be7da0051d8

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_table_axis_mem_setOf_xiBox_of_isUnitaryChar_of_mul_mul_rpow_eq

set_option autoImplicit false

noncomputable section

namespace TabBox

open scoped ComplexConjugate

theorem conj_eq_sq_div {A : ℂ} {r : ℝ} (hA : ‖A‖ = r) (h0 : A ≠ 0) : conj A = ((r ^ 2 : ℝ) : ℂ) / A := by
  have h := Complex.mul_conj A
  rw [Complex.normSq_eq_norm_sq, hA] at h
  rw [eq_div_iff h0, mul_comm]
  exact h

theorem conj_ofReal_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) : conj ((x : ℂ) ^ s) = (x : ℂ) ^ (conj s) := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem two_mul_sqrt_le {x : ℝ} (hx : 0 ≤ x) : 2 * Real.sqrt x ≤ x + 1 := by
  nlinarith [sq_nonneg (Real.sqrt x - 1), Real.sq_sqrt hx]

end TabBox

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open NumberField.TateGlobal AutomorphicForm TabBox
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (w : ℝ) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (t : ℝ),
    (fun v : HeightOneSpectrum (𝓞 K) => if v ∈ SK then (0 : ℂ × ℂ) else
      ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
          ((((μ * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
              (HeckeEigensystem.cNorm v) ^ (-((t : ℂ) * Complex.I)) +
            (((ν * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
              (HeckeEigensystem.cNorm v) ^ ((t : ℂ) * Complex.I)),
        (HeckeEigensystem.cNorm v) *
          (((μ * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
          (((ν * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ))) ∈
    {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
        (∀ v ∈ SK, x v = 0) ∧
        ∀ v ∉ SK,
          (x v).2 = HeckeEigensystem.cNorm v *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} := by
  intro αm hαm μ ν hμ hν hμν t

  have hαI : ∀ x : (AdeleRing (𝓞 K) K)ˣ, ((αm x : ℝˣ) : ℝ) = ideleNorm K x := fun _ => rfl
  simp only [Set.mem_setOf_eq]
  refine ⟨fun v hv => if_pos hv, fun v hv => ?_⟩
  simp only [if_neg hv]

  set d : (AdeleRing (𝓞 K) K)ˣ := Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v) with hd
  set q : ℕ := Ideal.absNorm v.asIdeal with hq_def
  have hq : 0 < q := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  set x : ℝ := (q : ℝ) with hx_def
  have hx : 0 < x := by rw [hx_def]; exact_mod_cast hq
  have hcN : HeckeEigensystem.cNorm v = ((x : ℝ) : ℂ) := by
    rw [hx_def, Complex.ofReal_natCast]
    rfl
  set c : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := cpowChar αm hαm (((w / 2 : ℝ) : ℂ)) with hc_def
  set A : ℂ := (((μ * c) d : ℂˣ) : ℂ) with hA_def
  set B : ℂ := (((ν * c) d : ℂˣ) : ℂ) with hB_def
  set ξd : ℂ := ((ξK ⟨d, Subgroup.mem_top d⟩ : ℂˣ) : ℂ) with hξd
  set r : ℝ := ideleNorm K d ^ (w / 2) with hr_def
  have hr : 0 < r := Real.rpow_pos_of_pos (ideleNorm_pos d) _

  have hcv : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((c z : ℂˣ) : ℂ) = ((ideleNorm K z : ℝ) : ℂ) ^ (((w / 2 : ℝ) : ℂ)) := by
    intro z
    rw [hc_def, cpowChar_apply_val, hαI z]
  have hcn : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((c z : ℂˣ) : ℂ)‖ = ideleNorm K z ^ (w / 2) := by
    intro z
    rw [hc_def, norm_cpowChar_apply, hαI z, Complex.ofReal_re]

  have hAn : ‖A‖ = r := by
    rw [hA_def, MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ d, one_mul, hcn]
  have hBn : ‖B‖ = r := by
    rw [hB_def, MonoidHom.mul_apply, Units.val_mul, norm_mul, hν d, one_mul, hcn]
  have hA0 : A ≠ 0 := fun h => hr.ne' (by rw [← hAn, h, norm_zero])
  have hB0 : B ≠ 0 := fun h => hr.ne' (by rw [← hBn, h, norm_zero])

  have hAB : A * B = ξd := by
    have h2 : (((ideleNorm K d : ℝ) : ℂ) ^ (((w / 2 : ℝ) : ℂ))) * (((ideleNorm K d : ℝ) : ℂ) ^ (((w / 2 : ℝ) : ℂ))) =
        ((ideleNorm K d ^ w : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleNorm_pos d).ne'),
        Complex.ofReal_cpow (ideleNorm_pos d).le]
      congr 1
      push_cast
      ring
    rw [hA_def, hB_def, MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, hcv]
    calc ((μ d : ℂˣ) : ℂ) * (((ideleNorm K d : ℝ) : ℂ) ^ (((w / 2 : ℝ) : ℂ))) *
          (((ν d : ℂˣ) : ℂ) * (((ideleNorm K d : ℝ) : ℂ) ^ (((w / 2 : ℝ) : ℂ))))
        = ((μ d : ℂˣ) : ℂ) * ((ν d : ℂˣ) : ℂ) *
            ((((ideleNorm K d : ℝ) : ℂ) ^ (((w / 2 : ℝ) : ℂ))) * (((ideleNorm K d : ℝ) : ℂ) ^ (((w / 2 : ℝ) : ℂ)))) := by
          ring
      _ = ((μ d : ℂˣ) : ℂ) * ((ν d : ℂˣ) : ℂ) * ((ideleNorm K d ^ w : ℝ) : ℂ) := by rw [h2]
      _ = ξd := hμν d
  have hξn : ‖ξd‖ = r * r := by rw [← hAB, norm_mul, hAn, hBn]

  have hcA : conj A = ((r ^ 2 : ℝ) : ℂ) / A := conj_eq_sq_div hAn hA0
  have hcB : conj B = ((r ^ 2 : ℝ) : ℂ) / B := conj_eq_sq_div hBn hB0

  have hc0 : ((x : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hx.le, ← Real.sqrt_eq_rpow]
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hr0 : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hX2n : ‖((x : ℝ) : ℂ) * A * B‖ = x * r * r := by
    rw [norm_mul, norm_mul, hAn, hBn, Complex.norm_of_nonneg hx.le]
  rw [hcN, Complex.cpow_neg, hc0]

  set e : ℂ := ((x : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) with he_def
  have hen : ‖e‖ = 1 := by
    rw [he_def, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      Real.rpow_zero]
  have he0 : e ≠ 0 := fun h => one_ne_zero (by rw [← hen, h, norm_zero])
  have hce : conj e = e⁻¹ := by
    rw [he_def, ← Complex.cpow_neg, conj_ofReal_cpow hx]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [mul_assoc, hAB]
  ·
    rw [hξn, Real.sqrt_mul_self hr.le]
    calc ‖((Real.sqrt x : ℝ) : ℂ) * (A * e⁻¹ + B * e)‖
        ≤ ‖((Real.sqrt x : ℝ) : ℂ)‖ * (‖A * e⁻¹‖ + ‖B * e‖) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = (2 * Real.sqrt x) * r := by
          rw [norm_mul, norm_mul, norm_inv, hen, hAn, hBn, Complex.norm_of_nonneg (Real.sqrt_nonneg x)]
          ring
      _ ≤ (x + 1) * r := mul_le_mul_of_nonneg_right (two_mul_sqrt_le hx.le) hr.le
  ·
    rw [hX2n]
    simp only [map_mul, map_add, map_inv₀, Complex.conj_ofReal, hcA, hcB, hce, inv_inv]
    push_cast
    field_simp
    ring

end S_AutomorphicForm_table_axis_mem_setOf_xiBox_of_isUnitaryChar_of_mul_mul_rpow_eq
end P2MW
export P2MW.S_AutomorphicForm_table_axis_mem_setOf_xiBox_of_isUnitaryChar_of_mul_mul_rpow_eq (solution)
