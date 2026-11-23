-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.orbital_integral_change_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:33.740552+00:00
-- url     : https://prove2.me/submissions/48aaf32e-8572-4f07-973f-788725e23521

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_sm_zero_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mul_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_ringInverse_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_psi_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_modK_unitR
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_modK_mul_isUnit
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_det_HH_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_det_ZZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_near_product_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_near_element_integral
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_antidiagonal_hessenberg_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_antidiagonal_hessenberg_mem_subgroup
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_inverse_determinant_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_product_of_shifted_coordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_GG_supp
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_near_inv
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
theorem _root_.solution (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) (m : ℕ)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ)
    (D' : Kˣ) (hD' : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q) (μ : K) (hμ : μ ∈ R)
    (x l : Fin m → K) (y l' : Pr (m + 1) → K)
    (hl : ∀ k, ∃ r ∈ R, l k = μ * (ϖ : K) ^ (b + 3 * ((m + 1) * a) + 2 * a + 1) * r)
    (hl' : ∀ p, ∃ r ∈ R, l' p = μ * (ϖ : K) ^ (b + 3 * ((m + 1) * a) + 2 * a + 1) * r)
    (hG : GG R ψ Φ (D' : K) x y ≠ 0) :
    GG R ψ Φ (D' : K) (x + l) (y + l') = GG R ψ Φ (D' : K) x y ∧
      ∃ r ∈ R, g0 (D' : K) (x + l) - g0 (D' : K) x = μ * r := by
  classical
  have hA := hC.adic
  have hϖ := hA.mem
  obtain ⟨hx, hy, hx0⟩ := GG_supp hC Φ hΦ D' hD' x y hG
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ = (m + 1) * a := ⟨_, rfl⟩
  rw [← ha₁] at hl hl' hx
  obtain ⟨c, hc⟩ : ∃ c, c = b + 2 * a₁ + 2 * a + 1 := ⟨_, rfl⟩
  have hb₁ : b + 3 * a₁ + 2 * a + 1 = c + a₁ := by omega
  rw [hb₁] at hl hl'
  obtain ⟨a0, ha0⟩ : ∃ a0 : K, a0 = μ * (ϖ : K) ^ c := ⟨_, rfl⟩
  have ha0R : a0 ∈ R := by rw [ha0]; exact R.mul_mem hμ (R.pow_mem hϖ c)
  have ha0I : a0 ∈ I R (ϖ : K) := by
    refine ⟨μ * (ϖ : K) ^ (b + 2 * a₁ + 2 * a), R.mul_mem hμ (R.pow_mem hϖ _), ?_⟩
    rw [ha0, hc, pow_succ]; ring
  have hsmall : ∀ s ∈ R, Sm R ϖ c (a0 * s) := fun s hs =>
    ⟨μ * s, R.mul_mem hμ hs, by rw [ha0]; ring⟩
  have hlS : ∀ k, Sm R ϖ (c + a₁) (l k) := fun k => by
    obtain ⟨r, hr, e1⟩ := hl k
    exact ⟨μ * r, R.mul_mem hμ hr, by rw [e1]; ring⟩
  have hlS' : ∀ p, Sm R ϖ (c + a₁) (l' p) := fun p => by
    obtain ⟨r, hr, e1⟩ := hl' p
    exact ⟨μ * r, R.mul_mem hμ hr, by rw [e1]; ring⟩
  have hU : ∀ k, IsUnit (x k) := fun k => (hx k).2.1
  obtain ⟨e, he⟩ : ∃ e : Fin m → K, e = fun k => Ring.inverse (x k) := ⟨_, rfl⟩
  have hxe : ∀ k, x k * e k = 1 := fun k => by rw [he]; exact Ring.mul_inverse_cancel _ (hU k)
  have heB : ∀ k, Bd R ϖ a₁ (e k) := fun k => by rw [he]; exact (hx k).2.2
  obtain ⟨ν, hνd⟩ : ∃ ν : Fin m → K, ν = fun k => 1 + l k * e k := ⟨_, rfl⟩
  have hν : ∀ k, Near R a0 (ν k) := by
    intro k
    obtain ⟨r, hr, e1⟩ := hl k
    refine ⟨r * ((ϖ : K) ^ a₁ * e k), R.mul_mem hr (heB k), ?_⟩
    rw [hνd, ha0]
    show 1 + l k * e k = _
    rw [e1, pow_add]; ring
  choose w hw using fun k => hA.near_inv ha0I (hν k)
  have hx' : ∀ k, (x + l) k = x k * ν k := by
    intro k
    rw [hνd]
    show x k + l k = x k * (1 + l k * e k)
    linear_combination (-(l k)) * hxe k
  have hx'e : ∀ k, (x + l) k * (e k * w k) = 1 := by
    intro k
    rw [hx' k]
    linear_combination (ν k * w k) * hxe k + (hw k).1
  have hU' : ∀ k, IsUnit ((x + l) k) := fun k => IsUnit.of_mul_eq_one _ (hx'e k)

  have hPE : (∏ k, x k) * ∏ k, e k = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun k _ => hxe k
  have hNW : (∏ k, ν k) * ∏ k, w k = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun k _ => (hw k).1
  have hP' : ∏ k, (x + l) k = (∏ k, x k) * ∏ k, ν k := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun k _ => hx' k
  obtain ⟨P, hP⟩ : ∃ P, P = ∏ k, x k := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ∏ k, e k := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = ∏ k, ν k := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = ∏ k, w k := ⟨_, rfl⟩
  rw [← hP, ← hE] at hPE
  rw [← hN, ← hW] at hNW
  rw [← hP, ← hN] at hP'
  have hNn : Near R a0 N := by rw [hN]; exact near_product_closed ha0R _ _ fun k _ => hν k
  have hWn : Near R a0 W := by rw [hW]; exact near_product_closed ha0R _ _ fun k _ => (hw k).2.1
  have hNR := near_element_integral ha0R hNn
  have hWR := near_element_integral ha0R hWn
  have hPNEW : P * N * (E * W) = 1 := by linear_combination (N * W) * hPE + hNW
  have hmod : modK R (P * N) = modK R P := by
    rw [modK_mul_isUnit hA (IsUnit.of_mul_eq_one _ hPE) (IsUnit.of_mul_eq_one _ hNW),
      modK_unitR hNR hWR hNW, mul_one]
  have hx0e : x0 (D' : K) x = (D' : K) * E := by
    unfold x0; rw [← hP, ringInverse_eq hPE]
  have hx0e' : x0 (D' : K) (x + l) = (D' : K) * E * W := by
    unfold x0; rw [hP', ringInverse_eq hPNEW]; ring
  have hx0B : Bd R ϖ a ((D' : K) * E) := by rw [← hx0e]; exact hC.L0 _ hx0
  obtain ⟨sW, hsW, hWs⟩ := hWn
  have hDD : (D' : K) * ((D'⁻¹ : Kˣ) : K) = 1 := by simp
  have hPB : Bd R ϖ (m * a) P := by
    rw [hP]
    have := Bd.prod (R := R) (ϖ := ϖ) (k := a) Finset.univ x fun j _ => hC.L0 _ (hx j).1
    simpa using this

  obtain ⟨et, het⟩ : ∃ et : Fin (m + 1) → K, et = Fin.cons (P * ((D'⁻¹ : Kˣ) : K)) e := ⟨_, rfl⟩
  obtain ⟨wt, hwt⟩ : ∃ wt : Fin (m + 1) → K, wt = Fin.cons N w := ⟨_, rfl⟩
  have hxt : ∀ j, xt (D' : K) x j * et j = 1 := by
    intro j
    rw [het]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [xt, Fin.cons_zero]
      rw [hx0e]
      linear_combination ((D' : K) * ((D'⁻¹ : Kˣ) : K)) * hPE + hDD
    · simp only [xt, Fin.cons_succ]
      exact hxe k
  have hxt' : ∀ j, xt (D' : K) (x + l) j * (et j * wt j) = 1 := by
    intro j
    rw [het, hwt]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [xt, Fin.cons_zero]
      rw [hx0e']
      linear_combination ((D' : K) * ((D'⁻¹ : Kˣ) : K) * (N * W)) * hPE +
        ((D' : K) * ((D'⁻¹ : Kˣ) : K)) * hNW + hDD
    · simp only [xt, Fin.cons_succ]
      exact hx'e k
  have hetB : ∀ j, Bd R ϖ a₁ (et j) := by
    intro j
    rw [het]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cons_zero]
      have := hPB.mul (inverse_determinant_bounded hC D' hD')
      have e1 : m * a + a = a₁ := by rw [ha₁]; ring
      rwa [e1] at this
    · simp only [Fin.cons_succ]
      exact heB k
  have hwtn : ∀ j, Near R a0 (wt j) := by
    intro j
    rw [hwt]
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [Fin.cons_zero] using hNn
    · simpa only [Fin.cons_succ] using (hw k).2.1

  have hg1 : g1 (D' : K) (x + l) (y + l') = g1 (D' : K) x y +
      ∑ i : Fin m, ((y (sd i) + l' (sd i)) * (W * wt i.castSucc * wt i.succ) - y (sd i)) *
        ((D' : K) * E * et i.castSucc * et i.succ) := by
    unfold g1
    rw [hx0e, hx0e', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ringInverse_eq (hxt i.castSucc), ringInverse_eq (hxt i.succ),
      ringInverse_eq (hxt' i.castSucc), ringInverse_eq (hxt' i.succ)]
    simp only [Pi.add_apply]
    ring
  have hdiff : ∑ i : Fin m, ((y (sd i) + l' (sd i)) * (W * wt i.castSucc * wt i.succ) - y (sd i)) *
        ((D' : K) * E * et i.castSucc * et i.succ) ∈ R := by
    refine R.sum_mem fun i _ => ?_
    have hlam : Near R a0 (W * wt i.castSucc * wt i.succ) :=
      (Near.mul ha0R ⟨sW, hsW, hWs⟩ (hwtn _)).mul ha0R (hwtn _)
    have hlamR := near_element_integral ha0R hlam
    obtain ⟨s, hs, hlams⟩ := hlam
    have hT : Bd R ϖ (a + a₁ + a₁) ((D' : K) * E * et i.castSucc * et i.succ) :=
      (hx0B.mul (hetB _)).mul (hetB _)
    have h1 : Sm R ϖ (0 + (a + a₁ + a₁)) (a0 * s * y (sd i)) := by
      have h2 : Sm R ϖ ((b + 2 * a₁ + a + 1) + a) (a0 * s) := by
        have := hsmall s hs
        have e1 : c = (b + 2 * a₁ + a + 1) + a := by omega
        rwa [e1] at this
      exact Sm.mono hϖ (by omega) (h2.mul_bd (hC.L0 _ (hy _)))
    have h3 : Sm R ϖ (0 + (a + a₁ + a₁)) (l' (sd i) * (W * wt i.castSucc * wt i.succ)) :=
      Sm.mono hϖ (by omega) ((hlS' _).mul_mem hlamR)
    have h4 := ((h1.add h3).mul_bd hT)
    have h5 := sm_zero_iff.1 h4
    have e2 : (y (sd i) + l' (sd i)) * (W * wt i.castSucc * wt i.succ) - y (sd i) =
        a0 * s * y (sd i) + l' (sd i) * (W * wt i.castSucc * wt i.succ) := by
      have : y (sd i) * (W * wt i.castSucc * wt i.succ) = y (sd i) * (1 + a0 * s) := by rw [hlams]
      linear_combination this
    rw [e2]
    exact h5
  have hψ : ψ (g1 (D' : K) (x + l) (y + l')) = ψ (g1 (D' : K) x y) := by
    rw [hg1, AddChar.map_add_eq_mul, psi_R hD hdiff, mul_one]

  have hδ0 : Sm R ϖ b ((D' : K) * E * W - (D' : K) * E) := by
    have h2 : Sm R ϖ ((b + 2 * a₁ + a + 1) + a) (a0 * sW) := by
      have := hsmall sW hsW
      have e1 : c = (b + 2 * a₁ + a + 1) + a := by omega
      rwa [e1] at this
    have h3 := Sm.mono hϖ (show b ≤ b + 2 * a₁ + a + 1 by omega) (h2.mul_bd hx0B)
    have e2 : (D' : K) * E * W - (D' : K) * E = a0 * sW * ((D' : K) * E) := by rw [hWs]; ring
    rw [e2]; exact h3
  have hΦeq : Φ (m + 1) (ZZ 0 (xt (D' : K) (x + l)) (y + l')) =
      Φ (m + 1) (ZZ 0 (xt (D' : K) x) y) := by
    have e1 : xt (D' : K) (x + l) = xt (D' : K) x + (xt (D' : K) (x + l) - xt (D' : K) x) := by
      simp
    rw [e1, antidiagonal_hessenberg_add]
    refine hΦ.2.2 _ _ ?_ (antidiagonal_hessenberg_mem_subgroup Λ₀ _ _ ?_ ?_)
    · have hp : ∏ j, xt (D' : K) x j = (D' : K) := by
        rw [product_of_shifted_coordinates, hx0e, ← hP]
        linear_combination (D' : K) * hPE
      rcases det_ZZ 0 (xt (D' : K) x) y with h | h <;> rw [h, det_HH_zero, hp]
      · exact hD'
      · rw [neg_neg]; exact hD'.symm
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Pi.sub_apply, xt, Fin.cons_zero]
        rw [hx0e, hx0e']
        exact hC.abelian₂ _ hδ0
      · simp only [Pi.sub_apply, xt, Fin.cons_succ, Pi.add_apply]
        rw [add_sub_cancel_left]
        exact hC.abelian₂ _ (Sm.mono hϖ (by omega) (hlS k))
    · intro p
      exact hC.abelian₂ _ (Sm.mono hϖ (by omega) (hlS' p))
  refine ⟨?_, ?_⟩
  · rw [GG, if_pos hU', GG, if_pos hU, hΦeq, hψ, hP', hmod, hP]
  · choose r hr hlr using hl
    refine ⟨∑ k, (ϖ : K) ^ (c + a₁) * r k + ((ϖ : K) ^ c * ((D' : K) * E)) * sW, ?_, ?_⟩
    · refine R.add_mem (R.sum_mem fun k _ => R.mul_mem (R.pow_mem hϖ _) (hr k)) (R.mul_mem ?_ hsW)
      exact Bd.mono hϖ (by omega) hx0B
    · unfold g0
      rw [hP', ← hP, ringInverse_eq hPE, ringInverse_eq hPNEW, mul_add, Finset.mul_sum]
      have e3 : ∑ k, (x + l) k = ∑ k, x k + ∑ k, μ * ((ϖ : K) ^ (c + a₁) * r k) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        show x k + l k = _
        rw [hlr k]; ring
      rw [e3, hWs, ha0]
      ring
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
