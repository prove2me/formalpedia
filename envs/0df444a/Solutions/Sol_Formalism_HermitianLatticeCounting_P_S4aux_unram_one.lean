-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.unram_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:55.665698+00:00
-- url     : https://prove2.me/submissions/dbaa9cac-d657-444a-87cd-6014b684c1b7

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
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
theorem _root_.solution (hU : Unram o O) : ∃ l : O →ₗ[o] o, l 1 = 1 := by
  classical
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let b := Module.Free.chooseBasis o O
  have hne : Nonempty (Module.Free.ChooseBasisIndex o O) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have := Module.finrank_eq_card_basis b
    rw [hU.rank2, Fintype.card_eq_zero] at this
    omega
  obtain ⟨i0⟩ := hne
  by_cases hex : ∃ i, IsUnit (b.repr 1 i)
  · obtain ⟨i, u, hu⟩ := hex
    refine ⟨((u⁻¹ : oˣ) : o) • b.coord i, ?_⟩
    rw [LinearMap.smul_apply, Module.Basis.coord_apply, ← hu, smul_eq_mul, Units.inv_mul]
  · exfalso
    push Not at hex
    have h1 : b i0 = ∑ j, b.repr 1 j • (b j * b i0) := by
      conv_lhs => rw [← one_mul (b i0), ← b.sum_repr 1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_mul_assoc]
    have h2 : (1 : o) = ∑ j, b.repr 1 j * b.repr (b j * b i0) i0 := by
      have := congrArg (fun z => b.repr z i0) h1
      simpa [map_sum, Finsupp.finsetSum_apply] using this
    have h3 : (1 : o) ∈ IsLocalRing.maximalIdeal o := by
      rw [h2]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hex j))
    exact (IsLocalRing.maximalIdeal.isMaximal o).ne_top ((Ideal.eq_top_iff_one _).2 h3)
end Formalism.HermitianLatticeCounting.P.S4aux
