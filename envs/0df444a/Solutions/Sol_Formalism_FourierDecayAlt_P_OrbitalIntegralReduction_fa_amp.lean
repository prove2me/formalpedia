-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fa_amp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:04.607803+00:00
-- url     : https://prove2.me/submissions/f50f7e67-f61b-47a2-aae5-b45651c0cddf

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bd_iff_sm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_GG_supp
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_mem_mulR
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (D' : Kˣ) (hD' : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q) {b₁ : ℕ}
    (hI : InvP R ψ ϖ Φ m (D' : K) b₁) :
    AmpHyp (mulR R ((ϖ⁻¹ ^ ((m + 1) * a) : Kˣ) : K)) (mulR R ((ϖ ^ b₁ : Kˣ) : K))
      (fun x : Fin m → K => bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) x)) := by
  have hϖ := hC.adic.mem
  have hmem : ∀ x : K, Bd R ϖ ((m + 1) * a) x → x ∈ mulR R ((ϖ⁻¹ ^ ((m + 1) * a) : Kˣ) : K) := by
    intro x hx
    obtain ⟨r, hr, e⟩ := bd_iff_sm_mul.1 hx
    exact fa_mem_mulR.2 ⟨r, hr, by rw [e]; simp⟩
  constructor
  · intro x hx k
    have : ∃ y, GG R ψ Φ (D' : K) x y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hx
      show bx R _ (Pr (m + 1)) (GG R ψ Φ (D' : K) x) = 0
      rw [bx_congr _ hcon, bx_zero]
    obtain ⟨y, hy⟩ := this
    obtain ⟨h1, -, -⟩ := GG_supp hC Φ hΦ D' hD' x y hy
    obtain ⟨h2, h3, h4⟩ := h1 k
    refine ⟨hmem _ (Bd.mono hϖ ?_ (hC.L0 _ h2)), h3, hmem _ h4⟩
    nlinarith
  · intro x l hl
    refine bx_congr _ fun y => ?_
    have := (hI 1 R.one_mem x l y 0 (fun k => by
      obtain ⟨r, hr, e⟩ := fa_mem_mulR.1 (hl k)
      exact ⟨r, hr, by rw [e]; simp⟩) (fun p => ⟨0, R.zero_mem, by simp⟩)).1
    simpa using this
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
