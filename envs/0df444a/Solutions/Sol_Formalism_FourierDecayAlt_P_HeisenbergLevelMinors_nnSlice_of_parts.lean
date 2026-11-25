-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.nnSlice_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:31:42.578798+00:00
-- url     : https://prove2.me/submissions/3f248308-3397-4edd-a1de-de8169421a05

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLevelMinors
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_intN
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_split_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Nset_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_matrix_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inv_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_isClosed_Nset
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs5_castW_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_big_cell_mem_holds
import Theorems.Thm_Formalism_QuantumDeterminants_big_cell_minors_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
theorem _root_.solution : NNMinor → NNVol → Formalism.FourierDecayAlt.P.JFxDs5.NNSlice := by
  intro hM hV k r Wp Wq _ _ _ _ D A m hThr c hc μ hμ
  have hnn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hT := hThr
  unfold TransportedAlt at hT
  rw [lt_div_iff₀ (by positivity)] at hT
  have hrm : 0 ≤ 6 * (r : ℝ) * (m : ℝ) := by positivity
  have hApos : 0 < A := by nlinarith
  have he0 : (0 : ℝ) < ((3 * (r + 1) : ℕ) : ℝ) := by positivity
  set β : ℝ := A / (2 * ((3 * (r + 1) : ℕ) : ℝ)) with hβ
  have hcast : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  have hβn : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < β := by
    rw [hβ, lt_div_iff₀ (by positivity), hcast]
    have : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ((r : ℝ) + 1) := by positivity
    nlinarith
  have hβ0 : 0 ≤ β := le_trans (sq_nonneg _) hβn.le
  have h2eβ : 2 * ((3 * (r + 1) : ℕ) : ℝ) * β = A := by rw [hβ]; field_simp
  have hg0G : bigCell k r c (castW μ) ∈ GV k r := big_cell_mem_holds k r c (castW μ) hc (JFxDs5.castW_mem hμ)
  have hmin := big_cell_minors_holds k r D.z D.z' c (castW μ) D.z_mem D.z'_mem
  have hD : ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r D.z D.z' (bigCell k r c (castW μ)) l ≠ 0 := by
    intro l hl
    have h := hmin.1 ⟨l.val, by omega⟩
    have hl' : (⟨(⟨l.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = l := Fin.ext rfl
    rw [← hl', h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  obtain ⟨Cm, hCm⟩ := hM k r D.z D.z' {bigCell k r c (castW μ)} isCompact_singleton
    (fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact ⟨hg0G, hD⟩)
  set Cm' : ℝ := max Cm 1 with hCmd
  have hCm' : 1 ≤ Cm' := le_max_right _ _
  have hCmle : Cm ≤ Cm' := le_max_left _ _
  clear_value Cm'
  have hsN := B5.haar_sigmaFinite D.haarN
  have hN := intN hV D.haarN hβn
  have ib : Integrable (fun nn : Mt k r × Mt k r => (Cm' ^ β * Cm' ^ β) *
      (gN (Matrix.of nn.1 : Mat k r) ^ (-β) * gN (Matrix.of nn.2 : Mat k r) ^ (-β))) (D.μN.prod D.μN) :=
    (hN.mul_prod hN).const_mul _
  have hae : ∀ᵐ nn ∂(D.μN.prod D.μN), (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
      (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae (B5.haar_ae D.haarN)).and
      (Measure.quasiMeasurePreserving_snd.ae (B5.haar_ae D.haarN))
  have c2 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} := B6.isClosed_Nset k r
  have hTc : IsClosed {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
      (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    (c2.preimage continuous_fst).inter (c2.preimage continuous_snd)
  have h1c : Continuous fun nn : Mt k r × Mt k r => (Matrix.of nn.1 : Mat k r) := continuous_fst
  have h2c : Continuous fun nn : Mt k r × Mt k r => (Matrix.of nn.2 : Mat k r) := continuous_snd
  have hy : ContinuousOn (fun nn : Mt k r × Mt k r =>
      (Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)
      {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
        (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    B6.continuousOn_matrix_mul (B6.continuousOn_matrix_mul
      ((B6.inv_continuousOn k r).comp h1c.continuousOn (fun nn h => B6.Nset_sub _ _ h.1)) continuousOn_const)
      h2c.continuousOn
  have hyG : ∀ nn ∈ {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
      (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r},
      (Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2 ∈ GV k r := fun nn h =>
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (B6.Nset_sub _ _ h.1)) hg0G) (B6.Nset_sub _ _ h.2)
  have hcont : ContinuousOn (fun nn : Mt k r × Mt k r =>
      gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (-A))
      {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
        (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    (B6.gN_continuous.comp_continuousOn hy).rpow_const fun nn h => Or.inl (B6.gN_pos (hyG nn h)).ne'
  have hmeas : AEStronglyMeasurable (fun nn : Mt k r × Mt k r =>
      gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (-A)) (D.μN.prod D.μN) := by
    have := hcont.aestronglyMeasurable (μ := D.μN.prod D.μN) hTc.measurableSet
    have hr : (D.μN.prod D.μN).restrict {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧
        (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} = D.μN.prod D.μN :=
      Measure.restrict_eq_self_of_ae_mem hae
    rwa [hr] at this
  refine Integrable.mono' ib hmeas ?_
  filter_upwards [hae] with nn hnn
  have hxG := hyG nn hnn
  have hx1 : 1 ≤ gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) := BetaSesquilinearity.gN_ge_one hxG
  obtain ⟨hm1, hm2⟩ := hCm _ (Set.mem_singleton _) _ hnn.1 _ hnn.2
  have hxp : 0 ≤ gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (3 * r) :=
    pow_nonneg (B6.gN_nonneg _) _
  have hpw : gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (3 * r) ≤
      gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (3 * (r + 1)) :=
    pow_le_pow_right₀ hx1 (by omega)
  have hsplit := split_bound (3 * (r + 1)) hx1 (B6.gN_pos (B6.Nset_sub _ _ hnn.1))
    (B6.gN_pos (B6.Nset_sub _ _ hnn.2)) (by linarith : (0 : ℝ) < Cm') hβ0
    (le_trans hm1 (le_trans (mul_le_mul_of_nonneg_right hCmle hxp)
      (mul_le_mul_of_nonneg_left hpw (by linarith))))
    (le_trans hm2 (le_trans (mul_le_mul_of_nonneg_right hCmle hxp)
      (mul_le_mul_of_nonneg_left hpw (by linarith))))
  rw [h2eβ] at hsplit
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (B6.gN_nonneg _) _)]
  exact hsplit
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
