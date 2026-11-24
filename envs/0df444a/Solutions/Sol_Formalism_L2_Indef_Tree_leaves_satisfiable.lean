-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.leaves_satisfiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:53.142524+00:00
-- url     : https://prove2.me/submissions/30fee8cb-ec41-421a-aeb5-251fddf8b792

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero
attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι
namespace Formalism.L2.Indef.Tree
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {d D : ℕ}
    (XW : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (M : Submodule (𝓞 K) (Fin d → K))
    (hXW : ∀ v, IsUnit (XW v).det) (hMfg : M.FG) (hM0 : M ≠ ⊥)
    (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n)
    (hχ : (∀ k : ℕ, χ k = ((jacobiSym k n : ℤ) : ℂ)) ∧ χ.IsPrimitive ∧ χ.Odd) (hper : PeriodIdentity n χ) :
    ∃ (P : SlopeBoundParameters) (F : SlopeBoundLiftData K P), LeafKL P ∧ LeafCN P ∧ LeafFE P ∧ LeafDiff P ∧ LeafNorm P ∧
      PageParams P ∧ FacParams 0 F ∧ LeafDegFlat 0 F ∧ LeafExport 0 F ∧ LeafCut F ∧ LeafShareBad F ∧
      LeafBadRows F ∧ LeafMuN F ∧ LeafLam F ∧ LeafRecord XW M F ∧ LeafNote2 0 F ∧
      LeafMeasure 0 (D := D) XW XW M P ∧ F.q' = 0 ∧ LeafDef 0 0 F ∧ P.m = 1 ∧
      F.pq = P.k + P.m - 1 - 2 * (F.q' : ℝ) := by
  obtain ⟨Zv, hKL, hCN, hFE⟩ := hper
  obtain ⟨μ, hμ⟩ : ∃ t : ℝ, t = muDef (Pi.basisFun K (Fin d)) XW M := ⟨_, rfl⟩
  obtain ⟨μx, hμx⟩ : ∃ t : ℝ, t = muMaxDef (Pi.basisFun K (Fin d)) XW M := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ t : ℝ, t = 13 + |LcOf χ| + |μ| := ⟨_, rfl⟩
  obtain ⟨x0, hx0⟩ : ∃ t : ℝ, t = Real.exp (Real.exp E) := ⟨_, rfl⟩
  have hE13 : 13 ≤ E := by rw [hE]; linarith [abs_nonneg (LcOf χ), abs_nonneg μ]
  have hexpE : E + 1 ≤ Real.exp E := Real.add_one_le_exp E
  have hx0E : Real.exp E + 1 ≤ x0 := by rw [hx0]; exact Real.add_one_le_exp _
  have hlx0 : Real.log x0 = Real.exp E := by rw [hx0, Real.log_exp]
  have hllx0 : Real.log (Real.log x0) = E := by rw [hlx0, Real.log_exp]
  have hx0pos : 0 < x0 := by rw [hx0]; exact Real.exp_pos _
  have hx14 : 14 ≤ x0 := by linarith
  have hL : x0 ^ (1 : ℝ) = x0 := Real.rpow_one x0
  have hb4 : 4 * |μ| ≤ Real.exp x0 := by
    have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ x0 by linarith)
    have hxμ : |μ| + 14 ≤ x0 := by linarith [abs_nonneg (LcOf χ)]
    nlinarith [abs_nonneg μ]
  have hbpos : 0 < Real.exp x0 := Real.exp_pos _
  have hb1 : 1 ≤ Real.exp x0 := Real.one_le_exp (by linarith)
  have hx7 : 3 ≤ x0 ^ ((1 : ℝ) / 7) := by
    rw [Real.rpow_def_of_pos hx0pos, hlx0]
    have h2 : 2 ≤ Real.exp E * (1 / 7) := by linarith
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    exact le_trans h3 (Real.exp_le_exp.mpr h2)
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hcut : M ⊓ (LinearMap.range (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K))).restrictScalars (𝓞 K) = M := by
    rw [LinearMap.range_id, Submodule.restrictScalars_top, inf_top_eq]
  have hbad : M ⊓ (LinearMap.ker (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K))).restrictScalars (𝓞 K) = ⊥ := by
    rw [LinearMap.ker_id, Submodule.restrictScalars_bot, inf_bot_eq]
  have hrk0 : rkK (⊥ : Submodule (𝓞 K) (Fin d → K)) = 0 := by
    unfold rkK; simp
  let P : SlopeBoundParameters :=
    { Pl := Unit, fPl := inferInstance, x := x0, eps := 1, rd := 4, v := 2, dN := n, dimNeZero := inferInstance, χ := χ,
      Z := Zv, logOmK := eulerConstantTerm n, logOm := eulerConstantTerm n - Real.log 4 + Real.log (Real.sqrt (n : ℝ)), f := 1, m := 1,
      k := 1, S := 1, η := 0, R := 0, PPp := 1, PPpp := 0, PP := |μ|, PPT := 0, Zpg := 0, nV := 0, Nr := 0,
      g12 := 1 }
  have hPL : P.L = x0 := hL
  have hPb : P.b = Real.exp x0 := by show Real.exp P.L = _; rw [hPL]
  let F : SlopeBoundLiftData K P :=
    { w := fun _ => 0, w0 := fun _ => 0, c1 := fun _ => -(P.logOm / 2), ua := fun _ => 1, kap := |μ| + |μx| + 1,
      q' := 0, pq := 1, ι := Unit, fι := inferInstance, nι := inferInstance, DY := 0, A := 1, cs := 0, X := 0,
      cc := 0, E0 := 0, Qcc := 0, ρ := 0, R1 := 0, R2 := 0, Bn := 1, δ' := 1, h := fun _ => 0,
      sl := fun _ => 0, δc := fun _ => 1, dc := fun _ => 1, degc := fun _ => 0, PPf := 0, mv := 0, muU := 0,
      nA := d, nB := d, nN := d, XA := XW, XB := XW, XN := XW, LA := M, LB := M, NN := M, Mk := M,
      φ := LinearMap.id, e := LinearMap.id, g := 1, PPh := 0, abelian₂ := 0, δ := 0, o' := 0, n2 := 0 }
  have hU : F.U = 1 := by show (∑ _τ : Unit, (1 : ℝ)) = 1; simp
  have hμ0 := abs_nonneg μ
  have hμx0 := abs_nonneg μx
  refine ⟨P, F, hKL, hCN, hFE, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ⟨le_rfl, (Real.exp_pos _).le⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, ?_, rfl, ?_⟩
  ·
    refine ⟨hχ.1, hχ.2.1, hχ.2.2, ?_, one_pos, le_rfl, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl,
      le_rfl, le_rfl, ?_, ?_, zero_le_one, le_rfl, ?_, ?_, ?_, ?_⟩
    · show 1 ≤ x0; linarith
    · show Real.log 4 ≤ P.L; rw [hPL]; linarith
    · show |LcOf χ| ≤ P.L; rw [hPL]; linarith [abs_nonneg μ]
    · show Real.log x0 ≤ P.L; rw [hPL, hlx0]; linarith
    · show 1 ≤ Real.log (Real.log x0); rw [hllx0]; linarith
    · show 3 ≤ x0 ^ ((1 : ℝ) / 7); exact hx7
    · show ((Fintype.card Unit : ℕ) : ℝ) ≤ 1; simp
    · show (1 : ℝ) * 1 ≤ P.b; rw [hPb]; linarith
    · show (1 : ℝ) * 0 ≤ P.b; rw [hPb]; linarith
    · show (1 : ℝ) * 0 ≤ P.b; rw [hPb]; linarith
    · show 20 * (1 : ℝ) * 0 ^ 2 * P.L ≤ 1; simp
    · show (0 : ℝ) ≤ P.b / 8; rw [hPb]; positivity
    · show |μ| + 2 * 0 * 0 ≤ P.b / 4; rw [hPb]; linarith
  ·
    refine ⟨fun _ => ⟨by norm_num, by norm_num⟩, by rw [hU], fun _ => ⟨le_rfl, ?_⟩, fun _ => by show |(0 : ℝ) - 0| ≤ 1 + 0; norm_num,
      by show |(1 : ℝ) - 1| ≤ 1; norm_num,
      Nat.cast_nonneg _, by show ((0 : ℕ) : ℝ) ≤ 1; norm_num, by show (1 : ℝ) ≤ |μ| + |μx| + 1; linarith, by show 0 * P.L ≤ |μ| + |μx| + 1; simp; linarith,
      by show 24 * (0 : ℝ) * _ ≤ P.b / 8; rw [hPb]; simp; positivity, by show 2 * (0 : ℝ) ≤ P.b / 8; rw [hPb]; simp; positivity⟩
    show (0 : ℝ) ≤ 2 * P.b; rw [hPb]; positivity
  · intro _
    show |-(P.logOm / 2) + 1 * P.logOm / 2| ≤ 0 * ((0 : ℕ) : ℝ) * Real.log 4
    rw [show -(P.logOm / 2) + 1 * P.logOm / 2 = 0 by ring]; simp
  · show |(∑ _τ : Unit, (0 : ℝ) * -(P.logOm / 2)) - 0 * ((0 : ℕ) : ℝ) * Real.log 4 * (∑ _τ : Unit, (0 : ℝ))| ≤
      1 * (|μ| + |μx| + 1)
    simp; linarith
  · refine ⟨hMfg, hMfg, hM0, hXW, le_rfl, LinearMap.id_comp _, fun _ _ _ => rfl, fun y hy => ?_, le_rfl, ?_⟩
    · show (((1 : ℕ) : ℕ) : K) • (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K)) y ∈ M
      simpa using hy
    · show Real.log ((1 : ℕ) : ℝ) ≤ 20 * 1 * 0 ^ 2 * P.L; simp
  · show ((rkK (M ⊓ (LinearMap.ker (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K))).restrictScalars (𝓞 K)) : ℕ) : ℝ)
      ≤ 3 * 0 * ((rkK M : ℕ) : ℝ)
    rw [hbad, hrk0]; simp
  · show |muDef (Pi.basisFun K (Fin d)) XW M| ≤ 2 * 1 * (|μ| + |μx| + 1); rw [← hμ]; linarith
  · show muMaxDef (Pi.basisFun K (Fin d)) XW M ≤ 2 * 1 * (|μ| + |μx| + 1); rw [← hμx]; linarith [le_abs_self μx]
  · refine ⟨?_, le_rfl⟩
    show muDef (Pi.basisFun K (Fin d)) XW
        (M ⊓ (LinearMap.range (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K))).restrictScalars (𝓞 K)) - 2 * (0 + 0)
      ≤ muDef (Pi.basisFun K (Fin d)) XW M
    rw [hcut]; linarith
  · refine ⟨le_rfl, ?_⟩; show (0 : ℝ) ≤ 0 * 1 * 0 ^ 2 * Real.log (0 * 4 * 1); simp
  · exact ⟨hXW, by simp⟩
  · show (∑ _τ : Unit, (0 : ℝ) * -(P.logOm / 2)) - 0 * P.LL0 * F.U - |μ| - (2 * 0 * 0 + 0 * P.L)
      ≤ muDef (Pi.basisFun K (Fin d)) XW M / 2
    rw [← hμ]; simp
    have := neg_abs_le μ; linarith
  · show (1 : ℝ) = 1 + 1 - 1 - 2 * ((0 : ℕ) : ℝ); norm_num
end Formalism.L2.Indef.Tree
