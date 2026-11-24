-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hj_norm_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:35.051575+00:00
-- url     : https://prove2.me/submissions/9f25dc10-4224-4bcb-9d54-4e835d299b17

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_exists_omega
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_basis
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_norm
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
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c)
    (h2 : Module.finrank F E = 2) (hfix : ∀ y : E, star y = y → ∃ c : F, algebraMap F E c = y)
    (x : E) : algebraMap F E (Algebra.norm F x) = x * star x := by
  obtain ⟨ω, hω⟩ := hj_exists_omega (F := F) (E := E) h2
  obtain ⟨β, h0, h1⟩ := hj_basis h2 ω hω
  obtain ⟨t, ht⟩ := hfix (ω + star ω) (by rw [star_add, star_star, add_comm])
  obtain ⟨nn, hnn⟩ := hfix (ω * star ω) (by rw [star_mul', star_star, mul_comm])
  have hst : star ω = algebraMap F E t - ω := by rw [ht]; ring
  have hω2 : ω * ω = algebraMap F E t * ω - algebraMap F E nn := by
    rw [hnn, hst]; ring
  rw [hj_decomp β ω h0 h1 x, hj_norm β ω h0 h1 t nn hω2]
  simp only [star_add, star_mul', hs, hst, map_add, map_mul, map_pow]
  linear_combination ((algebraMap F E (β.repr x 1)) ^ 2) * hω2
end Formalism.HermitianLatticeCounting.P.S4aux
