-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs5.slice1_of_nnSlice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:27.366903+00:00
-- url     : https://prove2.me/submissions/b398308c-792a-4869-ab8a-33ddb780e6a4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs5_castW_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Nset_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_matrix_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_of_contDiffOn_group
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inv_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_isClosed_Nset
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_big_cell_mem_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxDs5
theorem _root_.solution : NNSlice → Slice1 := by
  intro hS k r Wp Wq _ _ _ _ _ _ D A m F hThr hF c hc μ hμ
  obtain ⟨ν, hν⟩ := hF
  have hx : bigCell k r c (castW μ) ∈ GV k r := big_cell_mem_holds k r c (castW μ) hc (castW_mem hμ)
  have := B5.haar_sigmaFinite D.haarN
  have hae : ∀ᵐ nn ∂(D.μN.prod D.μN), (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae (B5.haar_ae D.haarN)).and
      (Measure.quasiMeasurePreserving_snd.ae (B5.haar_ae D.haarN))
  have c2 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} := B6.isClosed_Nset k r
  have hTc : IsClosed {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    (c2.preimage continuous_fst).inter (c2.preimage continuous_snd)
  have h1c : Continuous fun nn : Mt k r × Mt k r => (Matrix.of nn.1 : Mat k r) := continuous_fst
  have h2c : Continuous fun nn : Mt k r × Mt k r => (Matrix.of nn.2 : Mat k r) := continuous_snd
  have hy : ContinuousOn (fun nn : Mt k r × Mt k r => (Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)
      {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    B6.continuousOn_matrix_mul (B6.continuousOn_matrix_mul
      ((B6.inv_continuousOn k r).comp h1c.continuousOn (fun nn h => B6.Nset_sub _ _ h.1)) continuousOn_const)
      h2c.continuousOn
  have hyG : ∀ nn ∈ {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r},
      (Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2 ∈ GV k r := fun nn h =>
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (B6.Nset_sub _ _ h.1)) hx) (B6.Nset_sub _ _ h.2)
  have hcomp := (B6.continuousOn_of_contDiffOn_group hν.1).comp hy hyG
  have hmeas : AEStronglyMeasurable
      (fun nn : Mt k r × Mt k r => F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2))
      (D.μN.prod D.μN) := by
    have := hcomp.aestronglyMeasurable (μ := D.μN.prod D.μN) hTc.measurableSet
    have hr : (D.μN.prod D.μN).restrict
        {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} =
        D.μN.prod D.μN := Measure.restrict_eq_self_of_ae_mem hae
    rwa [hr] at this
  refine Integrable.mono' ((hS k r Wp Wq D A m hThr c hc μ hμ).const_mul ν) hmeas ?_
  filter_upwards [hae] with nn hnn
  have hyg := hyG nn hnn
  have hpos : 0 < gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) := B6.gN_pos hyg
  have hb := hν.2 [] [] (by simp) (by simp) (by simp) _ hyg
  change gN _ ^ A * ‖F _‖ ≤ ν at hb
  rw [Real.rpow_neg hpos.le]
  rw [mul_comm, ← le_div_iff₀ (Real.rpow_pos_of_pos hpos A)] at hb
  calc _ ≤ _ := hb
    _ = _ := by rw [div_eq_mul_inv]
end Formalism.FourierDecayAlt.P.JFxDs5
