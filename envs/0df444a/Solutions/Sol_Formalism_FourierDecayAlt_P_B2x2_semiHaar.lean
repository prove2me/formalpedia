-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.semiHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:27.259825+00:00
-- url     : https://prove2.me/submissions/2a430178-12e7-417a-a245-31a81bddffe7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_conjM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_rmulF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_compl_null
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_contOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_sfin
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_ae_of_compl
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_ae_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_ae_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_semi_group

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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution : SemiHaar := by
  intro k r A B μA μB ρ hA hB hn hcl hρ hρ' hμA hμB hconj
  have := sfin hμA
  have := sfin hμB
  refine ⟨semi_group A B hA hB hn hcl, ?_⟩
  have hm : Measurable (mulM : Mt k r × Mt k r → Mt k r) := mulM_cont.measurable
  have aeA : ∀ᵐ p ∂(μA.prod μB), (Matrix.of p.1 : Mat k r) ∈ A := ae_fst μA μB (A : Set (Mt k r)) hμA.conc
  have aeB : ∀ᵐ p ∂(μA.prod μB), (Matrix.of p.2 : Mat k r) ∈ B := ae_snd μA μB (B : Set (Mt k r)) hμB.conc
  have aeB' : ∀ᵐ b ∂μB, (Matrix.of b : Mat k r) ∈ B := ae_of_compl μB (B : Set (Mt k r)) hμB.conc

  have leftA : ∀ a ∈ A, ((μA.prod μB).map mulM).map (lmulM a) = (μA.prod μB).map mulM := by
    intro a ha
    rw [Measure.map_map (lmulM_cont a).measurable hm]
    have : (lmulM a ∘ mulM : Mt k r × Mt k r → Mt k r) = mulM ∘ Prod.map (lmulM a) id := by
      funext p
      exact (Matrix.mul_assoc a (Matrix.of p.1) (Matrix.of p.2)).symm
    rw [this, ← Measure.map_map hm ((lmulM_cont a).measurable.prodMap measurable_id),
      ← Measure.map_prod_map _ _ (lmulM_cont a).measurable measurable_id, hμA.left a ha, Measure.map_id]
  have rightB : ∀ b ∈ B, ((μA.prod μB).map mulM).map (rmulF b) = (μA.prod μB).map mulM := by
    intro b hb
    rw [Measure.map_map (rmulF_cont b).measurable hm]
    have : (rmulF b ∘ mulM : Mt k r × Mt k r → Mt k r) = mulM ∘ Prod.map id (rmulF b) := by
      funext p
      exact Matrix.mul_assoc (Matrix.of p.1) (Matrix.of p.2) b
    rw [this, ← Measure.map_map hm (measurable_id.prodMap (rmulF_cont b).measurable),
      ← Measure.map_prod_map _ _ measurable_id (rmulF_cont b).measurable, hμB.right b hb, Measure.map_id]
  have leftB : ∀ b ∈ B, ((μA.prod μB).map mulM).map (lmulM b) = (μA.prod μB).map mulM := by
    intro b hb
    rw [Measure.map_map (lmulM_cont b).measurable hm]
    have : (lmulM b ∘ mulM : Mt k r × Mt k r → Mt k r) = mulM ∘ Prod.map (conjM b) (lmulM b) := by
      funext p
      show b * (Matrix.of p.1 * Matrix.of p.2) = (b * Matrix.of p.1 * b⁻¹) * (b * Matrix.of p.2)
      have h : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul b (hB.unit b hb)
      calc b * (Matrix.of p.1 * Matrix.of p.2) = b * Matrix.of p.1 * (1 : Mat k r) * Matrix.of p.2 := by
            simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = (b * Matrix.of p.1 * b⁻¹) * (b * Matrix.of p.2) := by rw [← h]; simp only [Matrix.mul_assoc]
    rw [this, ← Measure.map_map hm ((conjM_cont b).measurable.prodMap (lmulM_cont b).measurable),
      ← Measure.map_prod_map _ _ (conjM_cont b).measurable (lmulM_cont b).measurable, hμB.left b hb, hconj b hb]
  have rightA : ∀ a ∈ A, ((μA.prod μB).map mulM).map (rmulF a) = (μA.prod μB).map mulM := by
    intro a₀ ha₀
    rw [Measure.map_map (rmulF_cont a₀).measurable hm]
    let g : Mt k r → Mt k r → Mt k r := fun b a => mulM (a, mulM (rmulF a₀ b, invM b))
    have hgm : Measurable (Function.uncurry g) := by
      apply hm.comp
      refine measurable_snd.prodMk (hm.comp ?_)
      exact ((rmulF_cont a₀).measurable.comp measurable_fst).prodMk (invM_meas.comp measurable_fst)
    have hg : ∀ᵐ b ∂μB, μA.map (g b) = μA := by
      filter_upwards [aeB'] with b hb
      exact hμA.right _ (hn b hb a₀ ha₀)
    have hT' := MeasurePreserving.skew_product (MeasurePreserving.id μB) hgm hg
    let T : Mt k r × Mt k r → Mt k r × Mt k r := fun p => (g p.2 p.1, p.2)
    have hT : MeasurePreserving T (μA.prod μB) (μA.prod μB) :=
      (Measure.measurePreserving_swap.comp hT').comp (Measure.measurePreserving_swap (μ := μA) (ν := μB))
    have hae : (rmulF a₀ ∘ mulM : Mt k r × Mt k r → Mt k r) =ᵐ[μA.prod μB] mulM ∘ T := by
      filter_upwards [aeB] with p hp
      show Matrix.of p.1 * Matrix.of p.2 * a₀ =
        (Matrix.of p.1 * (Matrix.of p.2 * a₀ * (Matrix.of p.2 : Mat k r)⁻¹)) * Matrix.of p.2
      have h : (Matrix.of p.2 : Mat k r)⁻¹ * Matrix.of p.2 = 1 := Matrix.nonsing_inv_mul _ (hB.unit _ hp)
      simp only [Matrix.mul_assoc]
      rw [h, Matrix.mul_one]
    rw [Measure.map_congr hae, ← Measure.map_map hm hT.measurable, hT.map_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine map_compl_null _ hcl _ _ hm ?_
    rw [← ae_iff (p := fun p : Mt k r × Mt k r => mulM p ∈ mulSet A B)]
    filter_upwards [aeA, aeB] with p h1 h2
    exact ⟨p.1, h1, p.2, h2, rfl⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    have : (lmulM (a * b) : Mt k r → Mt k r) = lmulM a ∘ lmulM b := by
      funext x; exact Matrix.mul_assoc a b (Matrix.of x)
    rw [this, ← Measure.map_map (lmulM_cont a).measurable (lmulM_cont b).measurable, leftB b hb, leftA a ha]
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    have : (rmulF (a * b) : Mt k r → Mt k r) = rmulF b ∘ rmulF a := by
      funext x; exact (Matrix.mul_assoc (Matrix.of x) a b).symm
    rw [this, ← Measure.map_map (rmulF_cont b).measurable (rmulF_cont a).measurable, rightA a ha, rightB b hb]
  · intro K hK
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    have hKB : IsCompact (ρ '' K ∩ (B : Set (Mt k r))) := (hK.image hρ).inter_right hB.closed
    have hKI : IsCompact (invM '' (ρ '' K ∩ (B : Set (Mt k r)))) :=
      hKB.image_of_continuousOn (invM_contOn.mono fun x hx => hB.unit x hx.2)
    have hKA : IsCompact (mulM '' (K ×ˢ (invM '' (ρ '' K ∩ (B : Set (Mt k r)))))) := (hK.prod hKI).image mulM_cont
    have hsub : (mulM ⁻¹' K : Set (Mt k r × Mt k r)) ≤ᵐ[μA.prod μB]
        (mulM '' (K ×ˢ (invM '' (ρ '' K ∩ (B : Set (Mt k r)))))) ×ˢ (ρ '' K ∩ (B : Set (Mt k r))) := by
      filter_upwards [aeA, aeB] with p h1 h2 hp
      have hb : p.2 ∈ ρ '' K ∩ (B : Set (Mt k r)) := ⟨⟨mulM p, hp, hρ' p.1 h1 p.2 h2⟩, h2⟩
      refine ⟨⟨(mulM p, invM p.2), ⟨hp, ⟨p.2, hb, rfl⟩⟩, ?_⟩, hb⟩
      show Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.2 : Mat k r)⁻¹ = Matrix.of p.1
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv (Matrix.of p.2 : Mat k r) (hB.unit _ h2), Matrix.mul_one]
    refine lt_of_le_of_lt (measure_mono_ae hsub) ?_
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (hμA.finite_compact _ hKA) (hμB.finite_compact _ hKB)
  · refine map_ne_zero _ _ hm ?_
    intro h0
    have h := congrArg (fun ν : Measure (Mt k r × Mt k r) => ν Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h
    rcases h with h | h
    · exact hμA.ne_zero (Measure.measure_univ_eq_zero.mp h)
    · exact hμB.ne_zero (Measure.measure_univ_eq_zero.mp h)
end Formalism.FourierDecayAlt.P.B2x2
