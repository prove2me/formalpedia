-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:40.9998+00:00
-- url     : https://prove2.me/submissions/ab2f4280-b9b2-4b4b-9636-116628928b50

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (hD : LocalDatum K R ψ) (d : R) (hd : IsUnit (d : K)) :
    Finite (R ⧸ Ideal.span {d}) := by
  have : CompactSpace R := isCompact_iff_compactSpace.1 hD.isCompact
  obtain ⟨u, hu⟩ := hd
  have hopen : IsOpen ((Ideal.span {d}).toAddSubgroup : Set R) := by
    have h1 : ((Ideal.span {d}).toAddSubgroup : Set R) =
        (fun x : R => ((u⁻¹ : Kˣ) : K) * (x : K)) ⁻¹' (R : Set K) := by
      ext x
      simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_preimage]
      rw [Ideal.mem_span_singleton']
      constructor
      · rintro ⟨c, rfl⟩
        rw [Subring.coe_mul, ← hu, mul_comm (c : K), ← mul_assoc, Units.inv_mul, one_mul]
        exact c.2
      · intro hx
        refine ⟨⟨_, hx⟩, ?_⟩
        apply Subtype.ext
        rw [Subring.coe_mul, ← hu]
        simp only
        rw [mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
    rw [h1]
    exact hD.isOpen.preimage (by fun_prop)
  exact AddSubgroup.quotient_finite_of_isOpen (Ideal.span {d}).toAddSubgroup hopen
end Formalism.FourierDecayAlt.P.A5x3
