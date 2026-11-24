-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallD.volume_ballSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:52.864894+00:00
-- url     : https://prove2.me/submissions/de4f8f90-48fa-457f-a4ab-af8f9d2ffdce

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscreteTopologyOfZsmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VolumeNormSqLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FundamentalDomainPiBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MeasurableSetBallSet
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallC_isClosed_ell
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallC_measurePreserving_psi
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallC_volume_ell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField NumberField.mixedEmbedding MeasureTheory Module Pointwise
open scoped Classical
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallD
open BallB BallC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [IsEmpty {w : InfinitePlace K // w.IsReal}] {h : V →ₗ⋆[K] V →ₗ[K] K}
  {b : Basis (Fin (finrank K V)) K V}
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallD
theorem _root_.solution
    (hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re) :
    volume.real (ballSet h b) =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ InfinitePlace.nrComplexPlaces K /
        ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re := by
  have hm : MeasurableSet (Set.pi Set.univ fun w : {w : InfinitePlace K // w.IsComplex} =>
      ell fun i => (w.1.embedding (h (b i) (b i))).re) :=
    (isClosed_set_pi fun _ _ => isClosed_ell _).measurableSet
  rw [measureReal_def, ballSet,
    (measurePreserving_psi K (Fin (finrank K V))).measure_preimage hm.nullMeasurableSet,
    volume_pi_pi, ENNReal.toReal_prod]
  have h1 : ∀ w : {w : InfinitePlace K // w.IsComplex},
      (volume (ell fun i => (w.1.embedding (h (b i) (b i))).re)).toReal =
        Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ) /
          ∏ i, (w.1.embedding (h (b i) (b i))).re := by
    intro w
    rw [volume_ell (hA w), ENNReal.toReal_ofReal]
    exact div_nonneg (by positivity) (Finset.prod_nonneg fun i _ => (hA w i).le)
  simp only [h1]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
end Formalism.HermitianLattices.Ext.L3.BallD
