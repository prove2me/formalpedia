-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.exists_frame_of_positive_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:11:59.715381+00:00
-- url     : https://prove2.me/submissions/b940f8cc-90ed-4854-bccf-69ae2a47072f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_symm
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_wb_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_normalize
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_perp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {a b : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hT : 0 < Tz k r b) :
    ∀ m, m ≤ k - 1 → ∃ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [a, b] Bs := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨Fin.elim0, ?_⟩
    unfold IsFrameOf
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨Bs, hB⟩ := ih (by omega)
    unfold IsFrameOf at hB
    obtain ⟨hB1, hB2, hB3⟩ := hB
    obtain ⟨v, hv0, hvw, hva, hvb, hvc⟩ := gb_perp (by omega) Bs a b
    obtain ⟨s, hs⟩ := gb_normalize hb hT hvw hvb hv0
    have hsv : inWb k r (s • v) := gb_wb_smul hvw s
    have h1 : ∀ i, herm (Hpk k r) (Bs i) (s • v) = 0 := by
      intro i
      rw [gb_smul_right, gb_symm (hB1 i) hvw, hvc i, star_zero, mul_zero]
    have h2 : ∀ i, herm (Hpk k r) (s • v) (Bs i) = 0 := by
      intro i
      rw [gb_smul_left, hvc i, mul_zero]
    refine ⟨Fin.snoc Bs (s • v), ?_⟩
    unfold IsFrameOf
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact hsv
      · rw [Fin.snoc_castSucc]; exact hB1 j
    · intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [Fin.snoc_last, if_pos rfl]; exact hs
      · rw [Fin.snoc_last, Fin.snoc_castSucc, h2, if_neg (Fin.castSucc_lt_last j').ne']
      · rw [Fin.snoc_last, Fin.snoc_castSucc, h1, if_neg (Fin.castSucc_lt_last i').ne]
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, hB2]
        by_cases h : i' = j' <;> simp [h]
    · intro i w hw
      have hw' := hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
        rcases hw' with rfl | rfl
        · rw [gb_smul_left, hva, mul_zero]
        · rw [gb_smul_left, hvb, mul_zero]
      · rw [Fin.snoc_castSucc]; exact hB3 j w hw
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
