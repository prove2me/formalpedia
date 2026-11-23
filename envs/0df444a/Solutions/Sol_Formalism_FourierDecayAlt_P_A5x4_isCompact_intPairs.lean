-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.isCompact_intPairs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:58.813246+00:00
-- url     : https://prove2.me/submissions/21691349-c472-41c2-81b2-6718478c2b7d

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_coe_inv_of_det
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_isClosed_lowW
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_isClosed_upUniG
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_lu_rec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_mem_lowW_iff
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_pt_mul_pt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Supp
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] (R : Subring K) (hRc : IsCompact (R : Set K)) (s : List ℕ) (t : ℕ → Kˣ) :
    IsCompact {p : lowW K s t × upUniG K s.sum |
      IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))} := by
  obtain ⟨Ph, Pu, hPh, hPu, hP⟩ := lu_rec (K := K) (n := s.sum)
  obtain ⟨wi, h1, h2⟩ : ∃ wi : Matrix (Fin s.sum) (Fin s.sum) K,
      wi * pt s t = 1 ∧ pt s t * wi = 1 :=
    ⟨pt s (fun b => (t b)⁻¹), pt_mul_pt s _ _ (fun b => by simp),
      pt_mul_pt s _ _ (fun b => by simp)⟩
  have hV : Continuous fun Z : Matrix (Fin s.sum) (Fin s.sum) K => pt s t * Ph (wi * Z) * wi :=
    (continuous_const.mul (hPh.comp (continuous_const.mul continuous_id))).mul continuous_const
  have hU : Continuous fun Z : Matrix (Fin s.sum) (Fin s.sum) K => Pu (wi * Z) :=
    hPu.comp (continuous_const.mul continuous_id)
  let Φ : Matrix (Fin s.sum) (Fin s.sum) K →
      (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) ×
        (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) :=
    fun Z => ((pt s t * Ph (wi * Z) * wi, MulOpposite.op (pt s t * Ph (wi * Z) * wi).adjugate),
      (Pu (wi * Z), MulOpposite.op (Pu (wi * Z)).adjugate))
  have hΦ : Continuous Φ :=
    (hV.prodMk (MulOpposite.continuous_op.comp hV.matrix_adjugate)).prodMk
      (hU.prodMk (MulOpposite.continuous_op.comp hU.matrix_adjugate))
  let ι : lowW K s t × upUniG K s.sum →
      (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) ×
        (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) :=
    fun p => (Units.embedProduct _ (p.1 : GL (Fin s.sum) K),
      Units.embedProduct _ (p.2 : GL (Fin s.sum) K))
  have hι : IsClosedEmbedding ι :=
    (Units.isClosedEmbedding_embedProduct.comp
      (isClosed_lowW s t wi h1 h2).isClosedEmbedding_subtypeVal).prodMap
      (Units.isClosedEmbedding_embedProduct.comp
        (isClosed_upUniG (K := K) s.sum).isClosedEmbedding_subtypeVal)
  let Mset : Set (Matrix (Fin s.sum) (Fin s.sum) K) := {Z | IsInt R Z}
  have hMc : IsCompact Mset := by
    have key : Mset = Set.univ.pi fun _ => Set.univ.pi fun _ => (R : Set K) := by
      ext Z
      show (∀ a b, Z a b ∈ R) ↔ _
      constructor
      · intro h
        exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => h i j
      · intro h a b
        exact Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h a) b
    rw [key]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  let S : Set (lowW K s t × upUniG K s.sum) :=
    {p | IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))}
  have hScl : IsClosed S :=
    hMc.isClosed.preimage (((Units.continuous_val.comp (continuous_subtype_val.comp
      continuous_fst)).mul continuous_const).mul
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)))
  have hSsub : S ⊆ ι ⁻¹' (Φ '' Mset) := by
    intro p hp
    refine ⟨_, hp, ?_⟩
    obtain ⟨hv1, hv2⟩ := (mem_lowW_iff s t wi h1 h2 p.1.1).1 p.1.2
    have hu : IsUpUni ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := p.2.2
    obtain ⟨e1, e2⟩ := hP _ _ hv2 hu
    have eY : wi * (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
        ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) =
        (wi * ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t) *
        ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := by
      simp only [Matrix.mul_assoc]
    have eV : pt s t * (wi * ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
        pt s t) * wi = ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := by
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    simp only [Φ, ι, eY, e1, e2, eV, Units.embedProduct_apply]
    rw [coe_inv_of_det _ (isLowUni_det K hv1), coe_inv_of_det _ (isUpUni_det K hu)]
  exact (hι.isCompact_preimage (hMc.image hΦ)).of_isClosed_subset hScl hSsub
end Formalism.FourierDecayAlt.P.A5x4
