-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.pick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:56.979688+00:00
-- url     : https://prove2.me/submissions/0cdd98a5-23ff-4d0e-a068-cdbc6c9e9d24

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_vR_apply
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_coe_det
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_sum_type

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
theorem _root_.solution (V : VF C) {ι : Type} [Fintype ι] (P : ι → Prop) {p n h : ℕ}
    (e : Fin p ≃ {x // P x}) (u : Fin n → ι → C) (hu : IsSat V u)
    (hsupp : ∀ c x, ¬ P x → u c x = 0) (ht : Fin h → ι → C) (ht_int : ∀ i x, V.Ge 0 (ht i x)) :
    ∃ (αR : Matrix (Fin p) (Fin h) (intR V)) (SR : Matrix (Fin n) (Fin p) (intR V))
      (WR : Matrix (Fin p) (Fin n) (intR V)), SR * WR = 1 ∧
      (∀ c i, (αR c i : C) = ht i (e c)) ∧
      ∀ f : Fin n → Fin h, vR V (Matrix.of fun k c => (SR * αR) c (f k)).det =
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, ht (f ρ) x * u c x).det := by
  obtain ⟨hu_int, w, hw_int, huw⟩ := hu
  refine ⟨Matrix.of fun c i => ⟨ht i (e c), ht_int i _⟩, Matrix.of fun c k => ⟨u c (e k), hu_int c _⟩,
    Matrix.of fun k c => ⟨w (e k) c, hw_int _ c⟩, ?_, fun c i => rfl, fun f => ?_⟩
  · ext c c'
    have hs := sum_type P e (fun x => u c x * w x c') (fun x hx => by rw [hsupp c x hx, zero_mul])
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    push_cast
    rw [hs, huw]
    split_ifs <;> simp
  · rw [vR_apply, coe_det]
    congr 2
    ext k c
    simp only [Matrix.of_apply, Matrix.mul_apply]
    push_cast
    have hs := sum_type P e (fun x => ht (f k) x * u c x) (fun x hx => by rw [hsupp c x hx, mul_zero])
    rw [← hs]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
