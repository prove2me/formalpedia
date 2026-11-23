-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_amp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:45.673218+00:00
-- url     : https://prove2.me/submissions/9d0e952c-a555-4a19-b9b1-eeb1626cabdb

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_subset
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_raise
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_of_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_sym_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_sym_univ
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_bdd_sym
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_sym_bdd
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_dil_sym
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_tsupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d N : ℕ) (hN : 2 ≤ N) {ρ : ℝ} (hρ : 0 < ρ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ R : ℝ, 1 ≤ R →
      Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 2 N K
        (fun x => cutB d 2 (R⁻¹ • x) * (cutB d ρ x - D_gau d δ x)) := by
  obtain ⟨MG, hMG0, hMG⟩ := D_gau_bound d N
  obtain ⟨Mχ, hMχ⟩ := D_cut_bound d N hρ
  obtain ⟨M2, hM2⟩ := D_cut_bound d N (two_pos : (0 : ℝ) < 2)
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ 0 0 (Nat.zero_le _))
  have hM20 : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0 0 (Nat.zero_le _))
  set Kχ := Mχ * (ρ + 1) ^ N with hKχ
  set K1 := 2 ^ N * Kχ * ((1 + MG) * (ρ + 1) ^ N) with hK1
  set K2 := 2 ^ N * (1 + Kχ) * MG / (ρ / 2) ^ 2 with hK2
  refine ⟨2 ^ N * (M2 * ((2 : ℝ) + 1) ^ N) * (K1 + K2), by positivity, ?_⟩
  intro δ hδ hδ1 σ hσ hσ1 R hR
  obtain ⟨hGb, hGs⟩ := hMG δ hδ hδ1 σ hσ hσ1
  have hw : ∀ x : Fin d → ℂ, 0 < wt σ x := fun x => D_wt_pos hσ x
  have hwA : ∀ (A : Set (Fin d → ℂ)), ∀ x ∈ A, 0 < wt σ x := fun _ x _ => hw x

  have hχ : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 0 N Kχ (cutB d ρ) := by
    have := D_dil_sym (D_cut_contDiff d hρ N) (D_cut_tsupport d hρ).le hρ.le hMχ (le_refl (1 : ℝ)) hσ hσ1
    simpa using this
  have hχR : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 0 N (M2 * ((2 : ℝ) + 1) ^ N)
      (fun x => cutB d 2 (R⁻¹ • x)) :=
    D_dil_sym (D_cut_contDiff d two_pos N) (D_cut_tsupport d two_pos).le two_pos.le hM2 hR hσ hσ1

  have h1G : Sym (Metric.closedBall (0 : Fin d → ℂ) ρ) (wt σ) 2 N ((1 + MG) * (ρ + 1) ^ N)
      (fun x => 1 - D_gau d δ x) := by
    have hb : Sym Set.univ (fun _ : Fin d → ℂ => (1 : ℝ)) 0 N (1 + MG) (fun x => 1 - D_gau d δ x) :=
      (Sym.const (1 : ℝ) zero_le_one (fun _ _ => one_pos) (fun _ _ => by simp)).sub
        (D_bdd_sym (D_gau_contDiff d δ N) hGb)
    have hle : ∀ x, D_gau d δ x ≤ 1 := by
      intro x
      unfold D_gau
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ∑ k, ‖x k‖ ^ 2 := by positivity
      nlinarith
    have h00 : D_gau d δ 0 = 1 := by simp [D_gau]
    have hfd : fderiv ℝ (fun x => 1 - D_gau d δ x) 0 = 0 := by
      apply IsLocalMin.fderiv_eq_zero
      refine Filter.Eventually.of_forall fun x => ?_
      simp only [h00]
      linarith [hle x]
    have := Sym.of_vanish (N := N) (σ := σ) (r := ρ) 2 hρ hσ hσ1 hN hb.1
      (fun x _ i hi => D_sym_bdd hb x i hi) (fun i hi => by
        interval_cases i
        · ext m
          simp [h00]
        · ext m
          rw [iteratedFDeriv_one_apply, hfd]
          simp)
    exact this
  have hb1 : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 2 N K1 (fun x => cutB d ρ x * (1 - D_gau d δ x)) := by
    have h := D_sym_cast (m' := 2) (by norm_num) (Sym.mul (hwA _) (hχ.subset (Set.subset_univ _)) h1G)
    refine D_sym_univ (m := 2) h ?_ (by positivity) hw
    rw [← D_cut_tsupport d hρ]
    exact tsupport_mul_subset_left
  have hb2 : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 2 N K2 (fun x => (1 - cutB d ρ x) * D_gau d δ x) := by
    have h1χ : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 0 N (1 + Kχ) (fun x => 1 - cutB d ρ x) :=
      (Sym.const (1 : ℝ) zero_le_one (hwA _) (fun _ _ => by simp)).sub hχ
    have h := (Sym.mul (hwA _) h1χ hGs).subset (Set.subset_univ {x : Fin d → ℂ | ρ / 2 ≤ ‖x‖})
    have h' := D_sym_cast (m' := 2) (by norm_num) (Sym.raise 2 (half_pos hρ) (fun x hx => by
      have : ρ / 2 ≤ ‖x‖ := hx
      unfold wt; linarith) h)
    refine D_sym_univ h' ?_ (by positivity) hw
    refine (tsupport_mul_subset_left).trans ?_
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
    intro x hx
    by_contra hlt
    have hlt' : ‖x‖ ≤ ρ / 2 := by
      have : ¬ ρ / 2 ≤ ‖x‖ := hlt
      linarith
    exact hx (by simp [D_cut_one d hρ hlt'])
  have hb := hb1.sub hb2
  have hfin := D_sym_cast (m' := 2) (by norm_num) (Sym.mul (hwA _) hχR hb)
  convert hfin using 2 with x
  ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
