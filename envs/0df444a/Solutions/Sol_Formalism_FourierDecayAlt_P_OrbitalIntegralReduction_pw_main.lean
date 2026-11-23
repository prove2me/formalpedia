-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:06.777799+00:00
-- url     : https://prove2.me/submissions/3a3a3c52-d48c-4dae-a5fa-513f114bc168

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_of_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_sm_zero_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_one_add_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_ringInverse_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hess_laplace
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_sg_units
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hess_one_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hess_two_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_isHess_HH
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_diagonal_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_entry_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_submatrix_tail
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_succ_above_one_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_succ_above_one_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_submatrix_above_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_determinant_and_inverse_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_entry_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_first_coordinate_formula
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hC : Cst R ϖ L₀ Λ₀ Q a b) (m : ℕ) (hm : 1 ≤ m) :
    ∃ M₂ : ℕ, ∀ t : Kˣ, Sm R ϖ M₂ (t : K) → ∀ D' : Kˣ, ((D' : K) ∈ Q ∨ -(D' : K) ∈ Q) →
    ∀ (ρ : K) (x : Fin m → K) (y : Pr (m + 1) → K),
      (∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k))) →
      (∀ p, y p ∈ L₀) → (HH (t : K) (Fin.cons ρ x : Fin (m + 1) → K) y).det = (D' : K) →
      Sm R ϖ b (ρ - x0 (D' : K) x) ∧
      ∃ r ∈ R, ρ * ((t⁻¹ : Kˣ) : K) = x0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + g1 (D' : K) x y + r := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ = (n + 1 + 1) * a := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = a + (n + 1) * a + (n + 1) * a₁ + 2 * a₁ := ⟨_, rfl⟩
  refine ⟨b + 3 * B + 1, ?_⟩
  intro t ht D' hD' ρ x y hx hy hdet
  rw [← ha₁] at hx
  have hϖ := hC.adic.mem
  obtain ⟨hDb, hDi⟩ := determinant_and_inverse_bounded hC D' hD'
  have htb : Bd R ϖ a (t : K) := ht.bd hϖ a
  have htR : (t : K) ∈ R := ht.mem hϖ
  have hxb : ∀ k, Bd R ϖ a (x k) := fun k => hC.L0 _ (hx k).1
  have hyb : ∀ p, Bd R ϖ a (y p) := fun p => hC.L0 _ (hy p)
  have hHess := isHess_HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y

  have lap := hess_laplace _ hHess
  rw [hdet, hessenberg_diagonal_entry, Fin.cons_zero] at lap

  obtain ⟨r₂, hr₂, e₂⟩ := hess_two_bd hϖ _ (hessenberg_submatrix_tail hHess) htb
    (fun i j => hessenberg_entry_bounded hϖ htb hxb i.succ j (fun h => hyb _))
  have hdiag : ∏ i, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
      Fin.succ Fin.succ) i i = ∏ k, x k := by
    simp only [Matrix.submatrix_apply, hessenberg_diagonal_entry, Fin.cons_succ]
  have hsg := sg_units ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
      Fin.succ Fin.succ) (fun i => Ring.inverse (x i)) (fun i => by
        simp only [Matrix.submatrix_apply, hessenberg_diagonal_entry, Fin.cons_succ]
        exact Ring.mul_inverse_cancel _ (hx i).2.1)
  have hsup : ∀ i : Fin n, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
      Fin.succ Fin.succ) i.castSucc i.succ = y (sd i.succ) := by
    intro i
    rw [Matrix.submatrix_apply, hessenberg_entry_upper _ _ _ (Fin.succ_lt_succ_iff.2 Fin.castSucc_lt_succ)]
    congr 1
  simp only [hsup] at hsg
  rw [hdiag] at hsg e₂
  rw [hsg] at e₂

  obtain ⟨r₁, hr₁, e₁⟩ := hess_one_bd hϖ _ (hessenberg_submatrix_above_one hHess) htb
    (fun i j => hessenberg_entry_bounded hϖ htb hxb (Fin.succAbove 1 i) j (fun h => hyb _))
  have hdiag' : ∏ i, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
      (Fin.succAbove 1) Fin.succ) i i = y (sd 0) * ∏ i : Fin n, x i.succ := by
    have f0 : ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
        (Fin.succAbove 1) Fin.succ) 0 0 = y (sd 0) := by
      rw [Matrix.submatrix_apply, succ_above_one_zero, hessenberg_entry_upper _ _ _ (Fin.succ_pos 0)]
      congr 1
    have f1 : ∀ i : Fin n, ((HH (t : K) (Fin.cons ρ x : Fin (n + 1 + 1) → K) y).submatrix
        (Fin.succAbove 1) Fin.succ) i.succ i.succ = x i.succ := by
      intro i
      rw [Matrix.submatrix_apply, succ_above_one_succ, hessenberg_diagonal_entry, Fin.cons_succ]
    rw [Fin.prod_univ_succ, f0]
    simp only [f1]
  rw [hdiag'] at e₁
  rw [e₂, e₁] at lap

  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i : Fin n, y (sd i.succ) * Ring.inverse (x i.castSucc) *
      Ring.inverse (x i.succ) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = ∏ k, x k := ⟨_, rfl⟩
  obtain ⟨P'', hP''def⟩ : ∃ P'', P'' = ∏ i : Fin n, x i.succ := ⟨_, rfl⟩
  obtain ⟨Pi, hPidef⟩ : ∃ Pi, Pi = ∏ k, Ring.inverse (x k) := ⟨_, rfl⟩
  have hPP : P * Pi = 1 := by
    rw [hPdef, hPidef, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => Ring.mul_inverse_cancel _ (hx k).2.1
  have hPsplit : P = x 0 * P'' := by rw [hPdef, hP''def, Fin.prod_univ_succ]
  have he0 : x 0 * Ring.inverse (x 0) = 1 := Ring.mul_inverse_cancel _ (hx 0).2.1
  have hP''Pi : P'' * Pi = Ring.inverse (x 0) := by
    rw [hPsplit] at hPP
    linear_combination (Ring.inverse (x 0)) * hPP - (P'' * Pi) * he0
  have hX0 : x0 (D' : K) x = (D' : K) * Pi := by
    unfold x0
    rw [← hPdef, ringInverse_eq hPP]
  have hg1 := first_coordinate_formula D' x y (fun k => (hx k).2.1)
  rw [← hS, hX0] at hg1
  rw [← hS, ← hPdef, ← hP''def] at lap
  rw [hX0, hg1]

  have hPi : Bd R ϖ ((n + 1) * a₁) Pi := by
    have := Bd.prod Finset.univ (fun k => Ring.inverse (x k)) (fun k _ => (hx k).2.2)
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [hPidef]; exact this
  have hSb : Bd R ϖ B S := by
    rw [hS]
    refine Bd.sum _ _ fun i _ => ?_
    exact Bd.mono hϖ (by omega) (((hyb (sd i.succ)).mul (hx i.castSucc).2.2).mul (hx i.succ).2.2)
  have hXb : Bd R ϖ B ((D' : K) * Pi) := Bd.mono hϖ (by omega) (hDb.mul hPi)
  have hq₂ : Bd R ϖ B (r₂ * Pi) := Bd.mono hϖ (by omega) (hr₂.mul hPi)
  have hq₁ : Bd R ϖ B (r₁ * Pi) := Bd.mono hϖ (by omega) (hr₁.mul hPi)
  have hye : Bd R ϖ B (y (sd 0) * Ring.inverse (x 0)) :=
    Bd.mono hϖ (by omega) ((hyb (sd 0)).mul (hx 0).2.2)
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = S - r₂ * Pi * (t : K) := ⟨_, rfl⟩
  have hδb : Bd R ϖ B δ := by rw [hδ]; exact hSb.sub (hq₂.mul_mem htR)
  have hε : Sm R ϖ 1 (-((t : K) * δ)) :=
    (Sm.mul_bd (Sm.mono hϖ (by omega) ht : Sm R ϖ (1 + B) (t : K)) hδb).neg
  obtain ⟨v, hv, ev, -⟩ := Sm.one_add_inv hC.adic le_rfl hε
  obtain ⟨G, hG⟩ : ∃ G, G = -((D' : K) * Pi * (r₂ * Pi)) + (D' : K) * Pi * δ * δ * v +
      y (sd 0) * Ring.inverse (x 0) * δ * v + r₁ * Pi * v := ⟨_, rfl⟩
  have hGb : Bd R ϖ (3 * B) G := by
    rw [hG]
    refine ((Bd.add ?_ ?_).add ?_).add ?_
    · exact Bd.mono hϖ (by omega) (hXb.mul hq₂).neg
    · exact Bd.mono hϖ (by omega) (((hXb.mul hδb).mul hδb).mul_mem hv)
    · exact Bd.mono hϖ (by omega) ((hye.mul hδb).mul_mem hv)
    · exact Bd.mono hϖ (by omega) (hq₁.mul_mem hv)
  have htG : (t : K) * G ∈ R :=
    sm_zero_iff.1 (Sm.mul_bd (Sm.mono hϖ (by omega) ht : Sm R ϖ (0 + 3 * B) (t : K)) hGb)

  have hW : ρ * (1 - (t : K) * δ) = (D' : K) * Pi + (t : K) * (y (sd 0) * Ring.inverse (x 0)) +
      (t : K) ^ 2 * (r₁ * Pi) := by
    rw [hδ]
    linear_combination (-Pi) * lap - ρ * (1 - (t : K) * S) * hPP + (t : K) * y (sd 0) * hP''Pi
  have hρ : ρ = ((D' : K) * Pi + (t : K) * (y (sd 0) * Ring.inverse (x 0)) +
      (t : K) ^ 2 * (r₁ * Pi)) * v := by
    linear_combination v * hW - ρ * ev
  have hfin : ρ = (D' : K) * Pi + (t : K) * (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S) +
      (t : K) ^ 2 * G := by
    rw [hG]
    have hδ' : S = δ + r₂ * Pi * (t : K) := by rw [hδ]; ring
    rw [hδ']
    linear_combination hρ + ((D' : K) * Pi * (1 + (t : K) * δ) +
      (t : K) * (y (sd 0) * Ring.inverse (x 0))) * ev
  have hgb : Bd R ϖ (2 * B) (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S + (t : K) * G) :=
    ((Bd.mono hϖ (by omega) hye).add (Bd.mono hϖ (by omega) (hXb.mul hSb))).add
      (Bd.of_mem hϖ htG _)
  constructor
  · have : ρ - (D' : K) * Pi =
        (t : K) * (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S + (t : K) * G) := by
      linear_combination hfin
    rw [this]
    exact Sm.mul_bd (Sm.mono hϖ (by omega) ht : Sm R ϖ (b + 2 * B) (t : K)) hgb
  · refine ⟨(t : K) * G, htG, ?_⟩
    have hti : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := by simp
    linear_combination ((t⁻¹ : Kˣ) : K) * hfin +
      (y (sd 0) * Ring.inverse (x 0) + (D' : K) * Pi * S + (t : K) * G) * hti
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
