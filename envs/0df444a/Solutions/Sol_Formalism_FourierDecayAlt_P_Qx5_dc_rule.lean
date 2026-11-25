-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.dc_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:50:53.773986+00:00
-- url     : https://prove2.me/submissions/0f33dbbe-709a-4c56-ab88-f325d91196fb

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_pairSum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {c : Mx k r → ℂ} {g : Mx k r} {ρ κ : Fin (mdim k r i) → ℂ} {s d : ℂ}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (h : ComRule k r i D E c g ρ κ s d) (hc : SmoothLev k r i D c) {t : ℕ}
    (a b : Fin t → Fin (mdim k r i)) (w : ℂ) {f : Mx k r → E} (hf : SmoothLev k r i D f) :
    Mop k r i a b w (fun y => c y • c y • f y) g =
      (2 * c g) • Mop k r i a b w (fun y => c y • f y) g - (c g ^ 2) • Mop k r i a b w f g := by
  have e1 := h t a b w (fun y => c y • f y) (smooth_mul hc hf)
  have e2 := h t a b w f hf
  have hp := pairSum t (ρ ∘ a) (ρ ∘ a) (κ ∘ b) (κ ∘ b) (fun l l' => Mop k r i (a ∘ l) (b ∘ l') (w - d - d) f g)
  have hz : ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * (ρ ∘ a) p * (κ ∘ b) q) •
        ∑ p' : Fin (t - 1), ∑ q' : Fin (t - 1),
          ((-1 : ℂ) ^ ((p' : ℕ) + (q' : ℕ)) * (ρ ∘ a) (skip1 p p') * (κ ∘ b) (skip1 q q')) •
            Mop k r i (a ∘ (skip1 p ∘ skip1 p')) (b ∘ (skip1 q ∘ skip1 q')) (w - d - d) f g = 0 := by
    rw [hp]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q _ =>
      Finset.sum_eq_zero fun q' _ => ?_
    split_ifs
    · rw [show (ρ ∘ a) p * (ρ ∘ a) p' - (ρ ∘ a) p' * (ρ ∘ a) p = 0 by ring]
      simp
    · rfl
  have e3 : ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) •
        Mop k r i (a ∘ skip1 p) (b ∘ skip1 q) (w - d) (fun y => c y • f y) g =
      c g • ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) •
        Mop k r i (a ∘ skip1 p) (b ∘ skip1 q) (w - d) f g := by
    simp only [h _ _ _ _ f hf, smul_add, Finset.sum_add_distrib]
    have : ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) • s •
        ∑ p' : Fin (t - 1), ∑ q' : Fin (t - 1),
          ((-1 : ℂ) ^ ((p' : ℕ) + (q' : ℕ)) * ρ ((a ∘ skip1 p) p') * κ ((b ∘ skip1 q) q')) •
            Mop k r i ((a ∘ skip1 p) ∘ skip1 p') ((b ∘ skip1 q) ∘ skip1 q') (w - d - d) f g = 0 := by
      have := congrArg (fun X => s • X) hz
      simp only [Finset.smul_sum, smul_zero] at this
      rw [← this]
      simp only [Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ =>
        Finset.sum_congr rfl fun q' _ => ?_
      simp only [smul_smul, Function.comp_apply]
      congr 1
      ring
    rw [this, add_zero, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_comm]
  rw [e3] at e1
  rw [e1]
  have e4 : s • ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) •
        Mop k r i (a ∘ skip1 p) (b ∘ skip1 q) (w - d) f g =
      Mop k r i a b w (fun y => c y • f y) g - c g • Mop k r i a b w f g := by
    rw [e2]; abel
  rw [smul_comm s, e4]
  module
end Formalism.FourierDecayAlt.P.Qx5
