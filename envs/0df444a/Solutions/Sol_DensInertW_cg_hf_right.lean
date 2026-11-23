-- Prove2me | solution 1 for DensInertW.cg_hf_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:28.924747+00:00
-- url     : https://prove2.me/submissions/8b670863-83f3-45ea-8c7d-7e1e8138ea78

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
theorem _root_.solution (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) (c : Fin m → L) (x : Fin n → L) (y : Fin m → Fin n → L) :
    hf (Fintype.card K) M x (∑ l, c l • y l) =
      ∑ l, c l ^ Fintype.card K * hf (Fintype.card K) M x (y l) := by
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
  have hfrob : ∀ b, (∑ l, c l * y l b) ^ Fintype.card K =
      ∑ l, c l ^ Fintype.card K * y l b ^ Fintype.card K := by
    intro b
    rw [hfr]
    simp [mul_pow]
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hfrob, Finset.mul_sum]
  calc _ = ∑ a, ∑ l, ∑ b, x a * M a b * (c l ^ Fintype.card K * y l b ^ Fintype.card K) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, x a * M a b * (c l ^ Fintype.card K * y l b ^ Fintype.card K) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => by ring
end DensInertW
