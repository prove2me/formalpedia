-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.vanishing_of_components_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:40:03.674635+00:00
-- url     : https://prove2.me/submissions/1bdbbb78-e232-4b74-ae1f-843c84a84382

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_id_inDDPlus
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_opApply_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_opOrder_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_bigPos_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_smoothCoef_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_commutes_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_inCC_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_op_supp
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_cut_supp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open DifferentialOperatorClasses
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.VanishingOfParts := by
  intro hV0 hBC hBA hVT hLD Cb hCb
  obtain ⟨c₃, hc₃, hV0⟩ := hV0
  obtain ⟨CV, hLD⟩ := hLD
  obtain ⟨C₁, hC₁⟩ := hBA Cb CV hCb
  obtain ⟨C₂, hC₂⟩ := hVT c₃ Cb hc₃ hCb
  refine ⟨3 * (max C₁ 0 + max C₂ 0), ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ D nf fib L o κ N As Θ ε de χ₀ A₀ F γ O hr hε hde hχ hfib hΘ hrad ho hκ hAs1 hAs2
    hA₀ hF hsupp hrel hG

  set n : ℕ := 2 * r + k + 1 with hn
  have hn3 : 3 ≤ n := by omega
  have hn' : 2 * r + 2 ≤ n + 1 := by omega
  have hsq : (n + 1) ^ 2 ≤ 3 * n ^ 2 := by nlinarith
  have hcu : (n + 1) ^ 3 ≤ 3 * n ^ 3 := by nlinarith
  have hA1 : N * (n + 1) ^ 2 ≤ 3 * As := by
    calc N * (n + 1) ^ 2 ≤ N * (3 * n ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = 3 * (N * n ^ 2) := by ring
      _ ≤ 3 * As := Nat.mul_le_mul_left _ hAs1
  have hA2 : (n + 1) ^ 3 ≤ 3 * As := le_trans hcu (Nat.mul_le_mul_left _ hAs2)
  have hNn : (0 : ℝ) ≤ Cb * N := by positivity
  have ho' : (o : ℝ) ≤ Cb * N * ((n + 1 : ℕ) : ℝ) := by
    refine le_trans ho ?_
    have : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    exact mul_le_mul_of_nonneg_left this hNn
  have hP : (0 : ℝ) ≤ ((r : ℝ) + 1) ^ 4 * As := by positivity
  have hAs3 : ((3 * As : ℕ) : ℝ) = 3 * (As : ℝ) := by push_cast; ring
  have hC1 : C₁ * ((r : ℝ) + 1) ^ 4 * ((3 * As : ℕ) : ℝ) ≤ A₀ := by
    rw [hAs3]
    have : C₁ * ((r : ℝ) + 1) ^ 4 * (3 * (As : ℝ)) ≤ 3 * (max C₁ 0 + max C₂ 0) * ((r : ℝ) + 1) ^ 4 * As := by
      have : C₁ * (((r : ℝ) + 1) ^ 4 * As) ≤ (max C₁ 0 + max C₂ 0) * (((r : ℝ) + 1) ^ 4 * As) :=
        mul_le_mul_of_nonneg_right (by have := le_max_left C₁ 0; have := le_max_right C₂ 0; linarith) hP
      nlinarith
    linarith
  have hC2 : C₂ * ((r : ℝ) + 1) ^ 4 * ((3 * As : ℕ) : ℝ) ≤ A₀ := by
    rw [hAs3]
    have : C₂ * ((r : ℝ) + 1) ^ 4 * (3 * (As : ℝ)) ≤ 3 * (max C₁ 0 + max C₂ 0) * ((r : ℝ) + 1) ^ 4 * As := by
      have : C₂ * (((r : ℝ) + 1) ^ 4 * As) ≤ (max C₁ 0 + max C₂ 0) * (((r : ℝ) + 1) ^ 4 * As) :=
        mul_le_mul_of_nonneg_right (by have := le_max_left C₂ 0; have := le_max_right C₁ 0; linarith) hP
      nlinarith
    linarith

  have hBud := hC₁ r (n + 1) N o κ (3 * As) A₀ hr hn' hA1 hA2 ho' hκ hC1
  have hThr := hC₂ r (n + 1) N o (3 * As) A₀ hr hn' hA1 hA2 ho' hC2

  have hcut : B.InCC (A₀ - 3 * ((r : ℝ) + 1) * ((o : ℝ) + 1)) (o + 1) (C6.cutAll D χ₀ de L F) := by
    have := hBC k r Wp Wq D nf fib L 0 0 [idTerm k r Wp Wq] ε de χ₀ A₀ F hε hde hχ hfib
      (id_inDDPlus D fib L) hF hsupp (o + 1)
    rw [opApply_id] at this
    have e : A₀ - ((0 : ℕ) : ℝ) - 3 * ((r : ℝ) + 1) * (((o + 1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)) =
        A₀ - 3 * ((r : ℝ) + 1) * ((o : ℝ) + 1) := by push_cast; ring
    rw [e] at this
    exact this
  have hord := opOrder_le D fib L o κ Θ hΘ

  have hbig : ∀ g ∈ C6.bigPos D, B.JF D (B.opApply Θ (C6.cutAll D χ₀ de L F)) g = 0 := by
    refine hV0 k r Wp Wq D Θ (A₀ - 3 * ((r : ℝ) + 1) * ((o : ℝ) + 1)) (C6.cutAll D χ₀ de L F)
      (smoothCoef_mono (bigPos_sub D L) hΘ.1) (commutes_mono D (bigPos_sub D L) hΘ.2.1) hrad ?_
      (inCC_mono (by omega) hcut)
    have h1 : (B.opOrder Θ : ℝ) ≤ o := by exact_mod_cast hord
    have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    have h3 : (B.opOrder Θ : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1 ≤ (o : ℝ) + r * ((n + 1 : ℕ) : ℝ) + 1 := by
      have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) r)
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ c₃ * ((r : ℝ) + 1) ^ 2)
    linarith

  have hcl := hBC k r Wp Wq D nf fib L o κ Θ ε de χ₀ A₀ F hε hde hχ hfib hΘ hF hsupp (C6.mmV CV r)
  refine hLD k r Wp Wq D (A₀ - κ - 3 * ((r : ℝ) + 1) * (((C6.mmV CV r : ℕ) : ℝ) + o)) ε (C6.mmV CV r)
    (B.opApply Θ (C6.cutAll D χ₀ de L F)) γ O hr hε ?_ le_rfl hcl
    (op_supp D Θ _ (cut_supp D χ₀ de L F hsupp)) hbig hrel hG
  refine le_trans ?_ hBud
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (α := ℝ) r)
  unfold C6.AV
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (α := ℝ) CV)
  have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have h0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (r : ℝ) ^ 3)
  have := mul_le_mul h2 h2 h0 (by positivity)
  nlinarith
end Formalism.FourierDecayAlt.P
