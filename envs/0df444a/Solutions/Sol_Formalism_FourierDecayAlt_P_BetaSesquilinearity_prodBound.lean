-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:11:01.130556+00:00
-- url     : https://prove2.me/submissions/626b7887-dc76-4908-8210-52abe1442cd8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_apz
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_leib_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sub_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_len_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_unit_lie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {O UU : Set (Mat k r)} (hO : IsOpen O) (hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ UU)
    {A d : ℝ} {m : ℕ} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E} {C c : ℝ}
    (ha : CkOn m UU a)
    (hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ O → ‖dLR u v a g‖ ≤ C * gN g ^ d)
    (hΦ : CCle (A + d) m Φ c) (hz : ∀ g ∈ GV k r, g ∈ O → Φ g = 0) :
    CCle A m (ap a Φ) (2 ^ m * (|C| * |c|)) := by
  have hP : Pr O UU m a Φ := ⟨ha, hΦ.1, hz⟩
  have hK : 0 ≤ |C| * |c| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨hP.ck hO hcov, fun u v hu hv hl g hg => ?_⟩
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hle : (((wL u ++ wR v).length : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by rw [len_LR]; exact_mod_cast hl
  rw [dLR_eq]
  by_cases hgO : g ∈ O
  · rw [Dw_vanish hO hlie (hP.mono zero_le).apz g hg hgO]
    simp only [norm_zero, mul_zero]
    positivity
  · have hp := gN_pos hg
    have hpA : 0 < gN g ^ A := Real.rpow_pos_of_pos hp _
    have hpd : 0 < gN g ^ d := Real.rpow_pos_of_pos hp _
    have hpAd : gN g ^ (A + d) = gN g ^ A * gN g ^ d := Real.rpow_add hp _ _
    have hb := leib_bound hO hcov g hg (|C| * gN g ^ d * (|c| / gN g ^ (A + d))) (wL u ++ wR v) a Φ hlie
      (hP.mono hle) (by
        intro w₁ w₂ h₁ h₂ hlen
        obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR h₁
        obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR h₂
        rw [len_LR, len_LR, len_LR] at hlen
        rw [← dLR_eq, ← dLR_eq]
        have b1 : ‖dLR u₁ v₁ a g‖ ≤ |C| * gN g ^ d :=
          (hab u₁ v₁ (fun X hX => hu X (hu₁.subset hX)) (fun X hX => hv X (hv₁.subset hX)) (by omega) g hg
            hgO).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpd.le)
        have b2 : ‖dLR u₂ v₂ Φ g‖ ≤ |c| / gN g ^ (A + d) := by
          rw [le_div_iff₀' (by rw [hpAd]; positivity)]
          exact (hΦ.2 u₂ v₂ (fun X hX => hu X (hu₂.subset hX)) (fun X hX => hv X (hv₂.subset hX)) (by omega)
            g hg).trans (le_abs_self _)
        exact mul_le_mul b1 b2 (norm_nonneg _) (by positivity))
    have hpow : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ m := by
      rw [len_LR]; exact pow_le_pow_right₀ (by norm_num) hl
    calc gN g ^ A * ‖Dw (wL u ++ wR v) (ap a Φ) g‖
        ≤ gN g ^ A * (2 ^ (wL u ++ wR v).length * (|C| * gN g ^ d * (|c| / gN g ^ (A + d)))) :=
          mul_le_mul_of_nonneg_left hb hpA.le
      _ = 2 ^ (wL u ++ wR v).length * (|C| * |c|) := by
          rw [hpAd]; field_simp
      _ ≤ 2 ^ m * (|C| * |c|) := mul_le_mul_of_nonneg_right hpow hK
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
