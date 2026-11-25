-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lemma_E_of_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:52.719453+00:00
-- url     : https://prove2.me/submissions/7f92314c-4f9b-4019-9aac-b81a74639064

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JC.LemmaEOfModel := by
  intro hE hLZ hGA hM
  obtain ⟨C₂, C₆, _hC₂, hC₆, hMod⟩ := hM
  refine ⟨C₆, hC₆, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ L j lam c Cm σ hB hsm hcut hmod
  refine hE hLZ hGA E Wp Wq S T f χ ν' m₀ top A₀ _ hB hsm (fun w v => ?_)
  obtain ⟨_hχ, _hCm, hσ, hSet, hDec, hAdj, hEig, hRR, hSys⟩ := hmod v
  have hadm : D.AdmAt S v (w.1 v) := ⟨w, rfl⟩
  obtain ⟨hA, hsz⟩ := hSys (C₂ * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2) (w.1 v) hadm
  have hlen : (w.1 v).length ≤ S.Ntop :=
    le_trans (Finset.le_sup (f := fun v => (w.1 v).length) (Finset.mem_univ v)) w.2.2
  have hN : S.G.r + 1 ≤ S.Ntop := by
    simp only [C.HidaSetting.Ntop, C.Kst]; omega
  have hT := hMod (D.parOf S v) (S.l + 1) (L v) (j v) (lam v) (S.cutLo v) (S.cutHi v) c S.Ntop hSet hDec hAdj hEig hN
    (hcut v) (w.1 v) hA hlen
  have h1 : Tendsto (fun ε : ℝ => σ v * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => σ v * ε) (𝓝 0) (𝓝 (σ v * 0)) :=
        ((continuous_const.mul continuous_id).tendsto 0)
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε using mul_pos hσ hε
  have h3 := (Complex.continuous_ofReal.tendsto _).comp ((hT.comp h1).const_mul (Cm v))
  have key : ∀ x : ℝ, (S.sizeAt v (w.1 v) * (Cm v * x) : ℝ) = Cm v * ((MA.sysQ (D.parOf S v) (S.l + 1) (L v) (j v)
      (lam v) (S.cutLo v) (S.cutHi v) (C₂ * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2) c S.Ntop).size (w.1 v) * x) :=
    fun x => by rw [hsz]; ring
  refine Tendsto.congr' (f₁ := fun ε => ((Cm v * MA.cutoffEnergyForm (D.parOf S v) (S.l + 1) (j v) c (σ v * ε) (w.1 v) : ℝ) : ℂ))
    ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hRR ε hε (w.1 v) hadm).symm
  · rw [key]
    exact h3
end Formalism.FourierDecayAlt.P
