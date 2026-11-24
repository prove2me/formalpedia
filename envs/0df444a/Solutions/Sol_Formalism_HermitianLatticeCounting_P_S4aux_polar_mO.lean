-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.polar_mO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:18.159847+00:00
-- url     : https://prove2.me/submissions/2e331c3c-a928-4a9e-8cec-02169af13a01

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_trace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_inj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_fixed
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_mem_mO_of_trace
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hU : Unram o O) {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
    (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O) (hH : IsHerm h) (C : Submodule O abelian₂)
    (hC : ∀ c ∈ C, ¬ IsUnit (h c c)) : ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ mO o O := by
  obtain ⟨T, hT⟩ := unram_trace hU
  have hnorm : ∀ c ∈ C, ∃ t ∈ IsLocalRing.maximalIdeal o, algebraMap o O t = h c c := by
    intro c hc
    obtain ⟨t, ht⟩ := unram_fixed hU (h c c) (hH c c).symm
    refine ⟨t, ?_, ht⟩
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    exact hC c hc (ht ▸ hu.map (algebraMap o O))
  intro c hc c' hc'
  apply mem_mO_of_trace hU T hT
  intro s
  obtain ⟨t1, ht1, e1⟩ := hnorm (s • c + c') (C.add_mem (C.smul_mem s hc) hc')
  obtain ⟨t2, ht2, e2⟩ := hnorm (s • c) (C.smul_mem s hc)
  obtain ⟨t3, ht3, e3⟩ := hnorm c' hc'
  have : T (s * h c c') = t1 - t2 - t3 := by
    apply unram_inj hU
    rw [hT, map_sub, map_sub, e1, e2, e3]
    have e4 : h c' (s • c) = star (s * h c c') := by
      rw [hH (s • c) c', map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [map_add, LinearMap.add_apply, e4]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.sub_mem _ ht1 ht2) ht3
end Formalism.HermitianLatticeCounting.P.S4aux
