-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.card_isoZZ_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:10.772734+00:00
-- url     : https://prove2.me/submissions/d80f6b22-7340-46d0-b573-94b678fec3da

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isoZZ_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isoZZ_trans
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {n n' m m' : ℕ} {A : Matrix (Fin n) (Fin n) K}
    {A' : Matrix (Fin n') (Fin n') K} {B : Matrix (Fin m) (Fin m) K}
    {B' : Matrix (Fin m') (Fin m') K}
    {φ1 : coker R A ≃ₗ[R] coker R A'} {φ2 : coker R B ≃ₗ[R] coker R B'}
    (h1 : φ1 ∈ isoZZ R A A') (h2 : φ2 ∈ isoZZ R B B') :
    Nat.card (isoZZ R A B) = Nat.card (isoZZ R A' B') := by
  refine Nat.card_congr ⟨fun φ => ⟨φ1.symm.trans (φ.1.trans φ2), ?_⟩,
    fun ρ => ⟨φ1.trans (ρ.1.trans φ2.symm), ?_⟩, ?_, ?_⟩
  · exact isoZZ_trans R (isoZZ_symm R h1) (isoZZ_trans R φ.2 h2)
  · exact isoZZ_trans R h1 (isoZZ_trans R ρ.2 (isoZZ_symm R h2))
  · intro φ; ext x; simp
  · intro ρ; ext x; simp
end Formalism.FourierDecayAlt.P.A5x4
