-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.dj_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:50.916265+00:00
-- url     : https://prove2.me/submissions/ddd012b8-b0b6-47a2-9498-dc8cab2771f8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dj_conjM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dj_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dj_levM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dj_aDil_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dj_conj_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dj_sigmaFinite

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (hU : HaarUnique) (hN : ClosedN) (hRec : NRecHaar) (hLev : DilLev) (hH : DilHeisMeas) (hK : KapRec)
    (k r' : ℕ) (μ' : Measure (Mt k r')) (hμ' : IsHaarOn (Nset k r') μ')
    (ih : ∀ t : ℝ, 0 < t → μ'.map (conjM (aDil k r' t)) = ENNReal.ofReal ((t ^ kap k r')⁻¹) • μ')
    (μN : Measure (Mt k (1 + r'))) (hμN : IsHaarOn (Nset k (1 + r')) μN) (t : ℝ) (ht : 0 < t) :
    μN.map (conjM (aDil k (1 + r') t)) = ENNReal.ofReal ((t ^ kap k (1 + r'))⁻¹) • μN := by
  have := dj_sigmaFinite hμ'
  have hvol : SFinite (volume : Measure (HPar k r')) := by rw [Measure.volume_eq_prod]; infer_instance
  have : SFinite (μHeis k r') := by
    unfold μHeis
    exact @MeasureTheory.Measure.instSFiniteMap _ _ _ _ _ _ hvol
  have hν := hRec k r' μ' hμ'
  obtain ⟨c, hc⟩ := hU k (1 + r') (Nset k (1 + r')) _ μN (hN _ _) hν hμN.conc hμN.left hμN.finite_compact
  have hca := (dj_conjM_cont (aDil k (1 + r') t)).measurable
  have hca' := (dj_conjM_cont (aDil k r' t)).measurable
  have hlev := (dj_levM_cont k r').measurable
  have hmul := (dj_mulM_cont (k := k) (r := 1 + r')).measurable
  have key : (((μHeis k r').prod (μ'.map (levM k r'))).map mulM).map (conjM (aDil k (1 + r') t)) =
      ENNReal.ofReal ((t ^ kap k (1 + r'))⁻¹) • ((μHeis k r').prod (μ'.map (levM k r'))).map mulM := by
    have h1 : (conjM (aDil k (1 + r') t) ∘ mulM : Mt k (1 + r') × Mt k (1 + r') → Mt k (1 + r')) =
        mulM ∘ Prod.map (conjM (aDil k (1 + r') t)) (conjM (aDil k (1 + r') t)) := by
      funext p
      exact dj_conj_mul _ (dj_aDil_unit _ _ _ ht.ne') p
    have h2 : (μ'.map (levM k r')).map (conjM (aDil k (1 + r') t)) =
        ENNReal.ofReal ((t ^ kap k r')⁻¹) • μ'.map (levM k r') := by
      rw [Measure.map_map hca hlev]
      have : (conjM (aDil k (1 + r') t) ∘ levM k r') = levM k r' ∘ conjM (aDil k r' t) := by
        funext x
        exact hLev k r' t ht.ne' (Matrix.of x)
      rw [this, ← Measure.map_map hlev hca', ih t ht, Measure.map_smul]
    rw [Measure.map_map hca hmul, h1, ← Measure.map_map hmul (hca.prodMap hca), ← Measure.map_prod_map _ _ hca hca,
      h2, hH k r' t ht, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, smul_smul,
      hK k r', pow_add, mul_inv, ENNReal.ofReal_mul (by positivity)]
  rw [hc, Measure.map_smul, key, smul_comm]
end Formalism.FourierDecayAlt.P.B2x8
