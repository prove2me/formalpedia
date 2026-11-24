-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.exists_pow_smul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:40.97828+00:00
-- url     : https://prove2.me/submissions/f5616b60-7160-4c55-97d9-67d5014fc2c2

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsPowSmulIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution {ϖ : O} (hϖ : Irreducible ϖ) (k : FractionRing O) :
    ∃ (n : ℕ) (a : O), (ϖ ^ n) • k = algebraMap O (FractionRing O) a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, a * ((w⁻¹ : Oˣ) : O), ?_⟩
  have hne : algebraMap O (FractionRing O) ((w : O) * ϖ ^ n) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hb0
  rw [Algebra.smul_def, ← mul_div_assoc, div_eq_iff hne, ← map_mul, ← map_mul]
  congr 1
  have : ((w⁻¹ : Oˣ) : O) * (w : O) = 1 := by simp
  calc ϖ ^ n * a = ϖ ^ n * a * (((w⁻¹ : Oˣ) : O) * (w : O)) := by rw [this, mul_one]
    _ = a * ((w⁻¹ : Oˣ) : O) * ((w : O) * ϖ ^ n) := by ring
end Formalism.RepresentationBoundsCohomology.LOC
