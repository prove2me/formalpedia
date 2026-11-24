-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.invariant_value_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:18.577078+00:00
-- url     : https://prove2.me/submissions/8cd27d50-493a-4cad-9324-ae61e01cd840

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_lower_sub
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_upper_sub
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_lower_det
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_upper_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorUnipotentInvariant := by
  intro R _ d Z l u q hl hu
  unfold leadingPrincipalMinor
  have hinj : Function.Injective (fun i : {i : Fin d // (i : ℕ) < q} => i.1) := Subtype.val_injective
  have hdown : ∀ (a : {i : Fin d // (i : ℕ) < q}) (x : Fin d), x ≤ a.1 →
      ∃ b : {i : Fin d // (i : ℕ) < q}, b.1 = x :=
    fun a x hx => ⟨⟨x, Nat.lt_of_le_of_lt hx a.2⟩, rfl⟩
  have hmono : StrictMono (fun i : {i : Fin d // (i : ℕ) < q} => i.1) := fun a b h => h
  rw [gf_upper_sub _ hinj hdown u hu (l * Z) _, gf_lower_sub _ hinj hdown l hl Z _, Matrix.det_mul,
    Matrix.det_mul, gf_lower_det _ hmono l hl, gf_upper_det _ hmono u hu, one_mul, mul_one]
end Formalism.HermitianLatticeCounting.P
