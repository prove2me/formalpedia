-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.geom_package
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:46.04458+00:00
-- url     : https://prove2.me/submissions/e40dd438-e687-4777-aaed-2fbfeb4e9710

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_exists_frame
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_exists_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_glev_herm
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_glev_inWb
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_glev_unit
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_not_prop_of_GG


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
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hGG : GGl k r z z' g ≠ 0) :
    ∃ (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (e' e : Fin (2 * r + k + 1) → ℂ),
      IsFrameOf k r [g⁻¹ *ᵥ z, z'] Bs ∧
      inWb k r e' ∧ herm (Hpk k r) e' z' = 0 ∧ herm (Hpk k r) e' e' = 1 ∧ IsFrameOf k r [z', e'] Bs ∧
      inWb k r e ∧ herm (Hpk k r) e z = 0 ∧ herm (Hpk k r) e e = 1 ∧
      IsFrameOf k r [z, e] (fun a => g *ᵥ Bs a) := by
  have hgi := glev_inWb hg hz
  have hgi' := glev_inWb hg hz'
  obtain ⟨hnp1, hnp2⟩ := not_prop_of_GG hz hz' hg hGG
  obtain ⟨_, hu2⟩ := glev_unit hg
  obtain ⟨Bs, hB⟩ := exists_frame hgi.2 hz' hT'
  obtain ⟨e', he'w, he'z, he'e, he'v⟩ := exists_unit hz' hT' hgi.2 hnp1
  obtain ⟨e, hew, hez, hee, hev⟩ := exists_unit hz hT hgi'.1 hnp2
  have hB' := hB
  unfold IsFrameOf at hB'
  obtain ⟨hB1, hB2, hB3⟩ := hB'
  have hBa : ∀ a, herm (Hpk k r) (Bs a) (g⁻¹ *ᵥ z) = 0 := fun a => hB3 a _ (by simp)
  have hBb : ∀ a, herm (Hpk k r) (Bs a) z' = 0 := fun a => hB3 a _ (by simp)
  have hgz : g *ᵥ (g⁻¹ *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hu2, Matrix.one_mulVec]
  have hgB : ∀ a, herm (Hpk k r) (g *ᵥ Bs a) z = 0 := by
    intro a
    have h1 := glev_herm hg (Bs a) (g⁻¹ *ᵥ z)
    rw [hgz] at h1
    rw [h1]
    exact hBa a
  refine ⟨Bs, e', e, hB, he'w, he'z, he'e, ?_, hew, hez, hee, ?_⟩
  · unfold IsFrameOf
    refine ⟨hB1, hB2, ?_⟩
    intro a v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with h | h
    · rw [h]; exact hBb a
    · rw [h]; exact he'v (Bs a) (hBa a) (hBb a)
  · unfold IsFrameOf
    refine ⟨fun a => (glev_inWb hg (hB1 a)).1, fun a b => ?_, ?_⟩
    · show herm (Hpk k r) (g *ᵥ Bs a) (g *ᵥ Bs b) = if a = b then 1 else 0
      rw [glev_herm hg]
      exact hB2 a b
    · intro a v hv
      show herm (Hpk k r) (g *ᵥ Bs a) v = 0
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with h | h
      · rw [h]; exact hgB a
      · rw [h]
        apply hev
        · rw [glev_herm hg]; exact hBb a
        · exact hgB a
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
