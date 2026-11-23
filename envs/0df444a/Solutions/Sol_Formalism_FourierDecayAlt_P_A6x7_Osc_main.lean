-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Osc.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:44.704036+00:00
-- url     : https://prove2.me/submissions/3768901e-eb67-42e1-8c95-307ad68a843b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_psi_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_tube
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_small_lat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Osc_inverse_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Osc_nhds_pi_box
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Osc_compact_box
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Osc
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x7.Osc
theorem _root_.solution : OscInvariant := by
  intro K _ _ _ R ψ hD h0 m L₁ Λ₁ hL₁ hΛ₁ A a D' hA
  let G : (Fin m → K) × ((Fin m → K) × (Fin m → K)) → K := fun p =>
    (∑ k, p.1 k + D' * (∏ k, (p.2.1 k - p.1 k * p.2.1 k * p.2.2 k) - ∏ k, p.2.1 k)) * a
  have hG : Continuous G := by
    dsimp only [G]; fun_prop
  obtain ⟨V, hV, hVG⟩ := tube G hG 0
    ({y : Fin m → K | ∀ k, y k ∈ (L₁ : Set K)} ×ˢ {y : Fin m → K | ∀ k, y k ∈ (L₁ : Set K)})
    ((compact_box _ hL₁.2).prod (compact_box _ hL₁.2)) (R : Set K) hD.isOpen (by
      intro y _
      have : G (0, y) = 0 := by simp [G]
      rw [this]; exact R.zero_mem)
  obtain ⟨W, hW, hWV⟩ := nhds_pi_box V hV
  obtain ⟨Λ, hΛ, hΛW⟩ := small_lat hD h0 (W ∩ (Λ₁ : Set K))
    (Filter.inter_mem hW (hΛ₁.1.mem_nhds Λ₁.zero_mem))
  refine ⟨Λ, hΛ, fun x l hl => ?_⟩
  have hAl : A (x + l) = A x := hA.2 x l fun i => (hΛW _ (hl i)).2
  show A (x + l) * ψ (g0 D' (x + l) * a) = A x * ψ (g0 D' x * a)
  rw [hAl]
  by_cases hx : A x = 0
  · rw [hx, zero_mul, zero_mul]
  congr 1
  have h1 := hA.1 x hx
  have h2 := hA.1 (x + l) (hAl ▸ hx)
  have key : g0 D' (x + l) * a = g0 D' x * a +
      G (l, (fun k => Ring.inverse (x k), fun k => Ring.inverse ((x + l) k))) := by
    have e : ∀ k, Ring.inverse (x k) - l k * Ring.inverse (x k) * Ring.inverse ((x + l) k) =
        Ring.inverse ((x + l) k) := by
      intro k
      have a1 : x k * Ring.inverse (x k) = 1 := Ring.mul_inverse_cancel _ (h1 k).2.1
      have a2 : (x k + l k) * Ring.inverse ((x + l) k) = 1 := Ring.mul_inverse_cancel _ (h2 k).2.1
      linear_combination (Ring.inverse ((x + l) k)) * a1 - Ring.inverse (x k) * a2
    have e' : ∏ k, (Ring.inverse (x k) - l k * Ring.inverse (x k) * Ring.inverse ((x + l) k)) =
        ∏ k, Ring.inverse ((x + l) k) := Finset.prod_congr rfl fun k _ => e k
    simp only [G, g0, inverse_prod]
    rw [e']
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  rw [key, AddChar.map_add_eq_mul,
    psi_R hD (hVG l (hWV l fun k => (hΛW _ (hl k)).1) _ ⟨fun k => (h1 k).2.2, fun k => (h2 k).2.2⟩),
    mul_one]
end Formalism.FourierDecayAlt.P.A6x7.Osc
