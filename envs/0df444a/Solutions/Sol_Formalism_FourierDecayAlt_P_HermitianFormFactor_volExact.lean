-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.volExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:16:34.824118+00:00
-- url     : https://prove2.me/submissions/447f6b02-aaa4-4289-b638-d232c08d1f4c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_bet_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_hsblock
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_frame_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_vol_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_ball_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Hdet
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution : VolExact := by
  intro k r μG hμ
  obtain ⟨Ep, Em, F⟩ := frame_exists k r
  have hH : IsUnit (Hpk k r).det := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Hdet k r
  have : IsFiniteMeasureOnCompacts μG := ⟨fun K hK => hμ.finite_compact K hK⟩
  have conc : ∀ᵐ g ∂μG, Matrix.of g ∈ UH (Hpk k r) := by rw [ae_iff]; exact hμ.conc
  have left : ∀ a ∈ UH (Hpk k r), μG.map (lmF a) = μG := fun a ha => hμ.left a ha
  have right : ∀ a ∈ UH (Hpk k r), μG.map (rmF a) = μG := fun a ha => hμ.right a ha
  have hset : ∀ ρ : ℝ, μG {g | gN (Matrix.of g) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) + 4 * ρ ^ 2} = μG (Bset Ep Em ρ) := by
    intro ρ
    refine measure_congr ?_
    filter_upwards [conc] with g hg
    have e1 := hsblock k r (Matrix.of g) hg
    have e2 := bet_eq F (Matrix.of g)
    refine propext ?_
    show gN (Matrix.of g) ^ 2 ≤ _ ↔ bet Ep Em (Matrix.of g) ≤ ρ ^ 2
    rw [e1, e2]
    constructor <;> intro h <;> linarith
  have hV : ∀ ρ : ℝ, 0 ≤ ρ → μG (Bset Ep Em ρ) =
      μG (invF ⁻¹' Bset Ep Em 1) * ENNReal.ofReal (ρ ^ (2 * (k + r) * (r + 1))) := by
    intro ρ hρ
    have := vol_core F hH μG conc left right hρ
    rwa [Fintype.card_fin, Fintype.card_fin] at this
  have hV1 : μG (invF ⁻¹' Bset Ep Em 1) = μG (Bset Ep Em 1) := by
    have := hV 1 zero_le_one
    rw [one_pow, ENNReal.ofReal_one, mul_one] at this
    exact this.symm
  have hfin : μG (invF ⁻¹' Bset Ep Em 1) ≠ ∞ := by
    rw [hV1, ← hset 1]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
      (hμ.finite_compact _ (isCompact_closedBall (0 : Mt k r) (((2 * r + k + 1 : ℕ) : ℝ) + 4 * 1 ^ 2))))
    intro g hg
    rw [mem_closedBall_zero_iff]
    refine ball_bound ?_ hg
    have : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hpos : μG (invF ⁻¹' Bset Ep Em 1) ≠ 0 := by
    intro h0
    apply hμ.ne_zero
    have hun : (Set.univ : Set (Mt k r)) = ⋃ N : ℕ, Bset Ep Em (N : ℝ) := by
      symm
      rw [Set.eq_univ_iff_forall]
      intro g
      obtain ⟨N, hN⟩ := exists_nat_ge (bet Ep Em (Matrix.of g))
      refine Set.mem_iUnion.mpr ⟨N + 1, ?_⟩
      show bet Ep Em (Matrix.of g) ≤ ((N + 1 : ℕ) : ℝ) ^ 2
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      push_cast
      nlinarith
    have : μG Set.univ = 0 := by
      rw [hun]
      refine measure_iUnion_null fun N => ?_
      rw [hV N (Nat.cast_nonneg _), h0, zero_mul]
    exact Measure.measure_univ_eq_zero.mp this
  refine ⟨(μG (invF ⁻¹' Bset Ep Em 1)).toNNReal, ENNReal.toNNReal_pos hpos hfin, fun ρ hρ => ?_⟩
  rw [hset ρ, hV ρ hρ, ENNReal.coe_toNNReal hfin]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
