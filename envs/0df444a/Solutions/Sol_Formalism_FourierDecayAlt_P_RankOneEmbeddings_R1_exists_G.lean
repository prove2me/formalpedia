-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.exists_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:45.737375+00:00
-- url     : https://prove2.me/submissions/40f05791-9a18-4300-93b6-a16c26243fd8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_factor_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_mvM_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
theorem _root_.solution (CWb : ClosedWb) (z' : Vc k r) (F : Mt k r → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ m : Mat k r, ∀ h ∈ UWset k r z', F (m * h : Mat k r) = F m) :
    ∃ G : Vc k r → ℝ≥0∞, Measurable G ∧ ∀ m ∈ UWb k r, F m = G (m *ᵥ z') := by
  obtain ⟨U, hUdef⟩ : ∃ U : Set (Mt k r), U = {m | (Matrix.of m : Mat k r) ∈ UWb k r} := ⟨_, rfl⟩
  have hUc : IsClosed U := by
    rw [hUdef]
    exact (CWb k r).closed
  haveI : PolishSpace U := hUc.polishSpace
  have h2 : ∀ x : Mt k r, x ∈ U → (Matrix.of x : Mat k r) ∈ UWb k r := by
    rw [hUdef]
    intro x hx
    exact hx
  have hmem : ∀ m : U, (Matrix.of (m : Mt k r) : Mat k r) ∈ UWb k r := fun m => h2 m m.2
  have hπ : Measurable fun m : U => (Matrix.of (m : Mt k r) : Mat k r) *ᵥ z' :=
    (mvM_cont.comp (continuous_subtype_val.prodMk continuous_const)).measurable
  have hF' : Measurable fun m : U => F m := hF.comp measurable_subtype_coe
  have hfib : ∀ x y : U, (Matrix.of (x : Mt k r) : Mat k r) *ᵥ z' = (Matrix.of (y : Mt k r) : Mat k r) *ᵥ z' →
      F x = F y := by
    rintro ⟨a, ha0⟩ ⟨b, hb0⟩ hxy
    have hW := CWb k r
    have hx' : (Matrix.of a : Mat k r) ∈ UWb k r := hmem ⟨a, ha0⟩
    have hy' : (Matrix.of b : Mat k r) ∈ UWb k r := hmem ⟨b, hb0⟩
    have hxy' : (Matrix.of a : Mat k r) *ᵥ z' = (Matrix.of b : Mat k r) *ᵥ z' := hxy
    have ha : IsUnit (Matrix.of a : Mat k r).det := hW.unit _ hx'
    have hg : (Matrix.of a : Mat k r)⁻¹ * Matrix.of b ∈ UWb k r := hW.mul_mem _ (hW.inv_mem _ hx') _ hy'
    have hgz : ((Matrix.of a : Mat k r)⁻¹ * Matrix.of b) *ᵥ z' = z' := by
      rw [← Matrix.mulVec_mulVec, ← hxy', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ha, Matrix.one_mulVec]
    have hgW : (Matrix.of a : Mat k r)⁻¹ * Matrix.of b ∈ UWset k r z' := ⟨hg.1, hg.2, hgz⟩
    have hab : (Matrix.of a : Mat k r) * ((Matrix.of a : Mat k r)⁻¹ * Matrix.of b) = Matrix.of b := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]
    have h1 := hinv (Matrix.of a) _ hgW
    rw [hab] at h1
    exact h1.symm
  obtain ⟨G, hG, hFG⟩ := factor_meas (fun m : U => (Matrix.of (m : Mt k r) : Mat k r) *ᵥ z') hπ
    (fun m => F m) hF' hfib
  refine ⟨G, hG, fun m hm => hFG ⟨m, ?_⟩⟩
  rw [hUdef]
  exact hm
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
