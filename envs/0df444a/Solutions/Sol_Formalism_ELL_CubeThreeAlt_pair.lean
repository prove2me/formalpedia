-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:45.146158+00:00
-- url     : https://prove2.me/submissions/d829b0ac-0c77-40bd-8307-bfb2091ea0b9

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_subst_mem
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_chordCoeffCubic_inversionDenom_inv
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_mul
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_slope_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_mvsubst_psubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
namespace CubeThreeAlt
open WeierstrassChordSeries
section Alg
variable {R : Type*} [CommRing R]
end Alg
section Mser
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
private theorem hasSubst_of_cc_zero_lemma {τ : Type} [Finite τ] {a : τ → MvPowerSeries σ K} (ha : ∀ i, cc (a i) = 0) :
    MvPowerSeries.HasSubst a := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
variable {w : PowerSeries K}
private theorem constantCoeff_subst_of_zero_lemma_2 {τ : Type} [Finite τ] {a : τ → MvPowerSeries σ K}
    (ha : ∀ i, cc (a i) = 0) (f : MvPowerSeries τ K) : cc (MvPowerSeries.subst a f) = cc f := by
  classical
  have hA : MvPowerSeries.HasSubst a := hasSubst_of_cc_zero_lemma ha
  rw [MvPowerSeries.constantCoeff_subst hA, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : cc (d.prod fun s e => a s ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.mpr hi)
      rw [map_pow, ha, zero_pow hi]
    rw [h0, smul_zero]
end Mser
end CubeThreeAlt
end Formalism.ELL
namespace Formalism.ELL
open CubeThreeAlt WeierstrassChordSeries
end Formalism.ELL
end
end

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
variable {w : PowerSeries K}
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution [Finite σ] (hw : WFixed W w) (a b : MvPowerSeries σ K) (ha : cc a = 0) (hb : cc b = 0)
    (haT : a ∈ TT W σ) (hbT : b ∈ TT W σ) :
    ∃ l n z A B : MvPowerSeries σ K,
      (b - a) * l = w.subst b - w.subst a ∧ n = w.subst a - l * a ∧
      chordCoeffCubicAt W l * A = 1 ∧ z = -a - b - chordCoeffQuadraticAt W l n * A ∧
      DDs W l n z * B = 1 ∧ MvPowerSeries.subst ![a, b] (F2 W w) = z * B ∧
      cc l = 0 ∧ l ∈ TT W σ ∧ A ∈ TT W σ ∧ B ∈ TT W σ := by
  have hab0 : ∀ i, cc (![a, b] i) = 0 := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
  have habT : ∀ i, ![a, b] i ∈ TT W σ := by
    intro i
    fin_cases i
    · exact haT
    · exact hbT
  have hab : MvPowerSeries.HasSubst ![a, b] := hasSubst_of_cc_zero_lemma hab0
  set φ : MvPowerSeries (Fin 2) K →ₐ[K] MvPowerSeries σ K := MvPowerSeries.substAlgHom hab with hφdef
  have hφ : ∀ f, φ f = MvPowerSeries.subst ![a, b] f := fun f => by
    rw [hφdef, MvPowerSeries.coe_substAlgHom]
  have hX0 : φ (MvPowerSeries.X 0) = a := by simp [hφ, MvPowerSeries.subst_X hab]
  have hX1 : φ (MvPowerSeries.X 1) = b := by simp [hφ, MvPowerSeries.subst_X hab]
  have hC : ∀ c : K, φ (MvPowerSeries.C c) = MvPowerSeries.C c := fun c => by
    simpa [MvPowerSeries.algebraMap_apply] using φ.commutes c
  have hW : ∀ i : Fin 2, φ (Formalism.ELL.WeierstrassChordSeries.Wi w i) = w.subst (![a, b] i) := fun i => by
    rw [hφ, Formalism.ELL.WeierstrassChordSeries.Wi, Formalism.ELL.WeierstrassSubstitution.mvsubst_psubst w _ (MvPowerSeries.constantCoeff_X i) _ hab, MvPowerSeries.subst_X hab]
  have hmem : ∀ f, f ∈ Formalism.ELL.WeierstrassChordSeries.T W → φ f ∈ TT W σ := fun f hf => by
    rw [hφ]
    exact subst_mem hf habT hab0
  obtain ⟨hAi, hDi, hAT, hDT⟩ := chordCoeffCubic_inversionDenom_inv hw
  refine ⟨φ (Formalism.ELL.WeierstrassChordSeries.lam w), φ (Formalism.ELL.WeierstrassChordSeries.nu w), φ (Formalism.ELL.WeierstrassChordSeries.z3 W w), φ (Formalism.ELL.WeierstrassChordSeries.C3 W w)⁻¹,
    φ (Formalism.ELL.WeierstrassChordSeries.dd W w)⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg φ (Formalism.ELL.WeierstrassChordSeries.lam_mul w)
    rw [map_mul, map_sub, map_sub, hX0, hX1, hW, hW] at h
    simpa using h
  · simp [Formalism.ELL.WeierstrassChordSeries.nu, hW, hX0]
  · have h := congrArg φ hAi
    rw [map_mul, map_one] at h
    simpa only [chordCoeffCubicAt, Formalism.ELL.WeierstrassChordSeries.C3, Formalism.ELL.WeierstrassChordSeries.c3, Formalism.ELL.WeierstrassChordSeries.ca, map_add, map_mul, map_pow,
      map_one, hC] using h
  · simp only [Formalism.ELL.WeierstrassChordSeries.z3, chordCoeffQuadraticAt, Formalism.ELL.WeierstrassChordSeries.C2, Formalism.ELL.WeierstrassChordSeries.c2, Formalism.ELL.WeierstrassChordSeries.ca, map_sub,
      map_neg, map_add, map_mul, map_pow, map_ofNat, hC, hX0, hX1]
  · have h := congrArg φ hDi
    rw [map_mul, map_one] at h
    simpa only [DDs, Formalism.ELL.WeierstrassChordSeries.dd, Formalism.ELL.WeierstrassChordSeries.w3, Formalism.ELL.WeierstrassChordSeries.ca, map_add, map_mul, map_neg, map_one,
      hC] using h
  · rw [← hφ, Formalism.ELL.WeierstrassChordSeries.F2, map_mul]
  · rw [hφ, constantCoeff_subst_of_zero_lemma_2 hab0, Formalism.ELL.WeierstrassChordSeries.lam_cc hw]
  · exact hmem _ (Formalism.ELL.WeierstrassChordSeries.slope_mem_integralSeries hw)
  · exact hmem _ hAT
  · exact hmem _ hDT
end Formalism.ELL.CubeThreeAlt
