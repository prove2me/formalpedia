-- Prove2me | solution 1 for DensInertW.cg_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:30.319846+00:00
-- url     : https://prove2.me/submissions/548434a9-4053-41b6-8107-4d85b7cfdfeb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open DensInertW
namespace DensInertW
theorem _root_.solution (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m : ℕ}
    (A C : Matrix (Fin m) (Fin m) L) :
    (A * C).map (fun y => y ^ Fintype.card K) =
      A.map (fun y => y ^ Fintype.card K) * C.map (fun y => y ^ Fintype.card K) := by
  obtain ⟨p, hch⟩ := CharP.exists K
  obtain ⟨n, hp, hq⟩ := FiniteField.card K p
  haveI := Fact.mk hp
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hfr : ∀ (s : Finset (Fin m)) (f : Fin m → L),
      (∑ i ∈ s, f i) ^ Fintype.card K = ∑ i ∈ s, f i ^ Fintype.card K := by
    intro s f
    rw [hq]
    first
    | exact sum_pow_char_pow s f
    | (haveI : ExpChar L p := ExpChar.prime hp
       have h := map_sum (iterateFrobenius L p n) f s
       simp only [iterateFrobenius_def] at h
       exact h)
    | (haveI : ExpChar L p := ExpChar.prime hp
       simp)
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [hfr]
  simp [mul_pow]
end DensInertW
