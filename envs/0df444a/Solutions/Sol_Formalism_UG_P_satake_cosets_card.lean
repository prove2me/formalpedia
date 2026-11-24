-- Prove2me | solution 1 for Formalism.UG.P.satake_cosets_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:08:20.890995+00:00
-- url     : https://prove2.me/submissions/e01fd726-3669-41f6-9f53-3595912df6cf

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satake_Tj_ne_zero_iff
import Theorems.Thm_Formalism_UG_P_satake_prodD_ne
import Theorems.Thm_Formalism_UG_P_prod_pow_sub_one_ne_zero
import Theorems.Thm_Formalism_UG_P_satake_qbinom
import Theorems.Thm_Formalism_UG_P_satake_two_le_qV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (hTjCosets : TjCosets) {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v)
    (hu : IsUnifV F v ϖ) {j : ℕ} (hj : j ≤ n) :
    {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j}.Finite ∧
    {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j}.ncard =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, qV F v ^ satakeInv Finset.univ S := by
  have hq : (2 : ℤ) ≤ qV F v := by exact_mod_cast satake_two_le_qV v
  have h := hTjCosets F v n ϖ hϖ hu j hj
  have hset : {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
      Tj ℤ n (Ov F v) ϖ j x.out ≠ 0} =
      {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j} := by
    ext x; exact satake_Tj_ne_zero_iff v ℤ ϖ j x.out
  rw [hset] at h
  have hb := satake_qbinom (qV F v : ℤ) (Finset.univ : Finset (Fin n)) j
  rw [Finset.card_univ, Fintype.card_fin, ← h] at hb
  have hD := satake_prodD_ne hq j
  have hc : (Nat.card {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
      x.out ∈ satakeTset v ϖ j} : ℤ) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, (qV F v : ℤ) ^ satakeInv Finset.univ S :=
    (mul_right_cancel₀ hD hb).symm
  have hne : Nat.card {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
      x.out ∈ satakeTset v ϖ j} ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, zero_mul] at h
    exact prod_pow_sub_one_ne_zero hq hj h.symm
  refine ⟨Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero hne), ?_⟩
  rw [← Nat.card_coe_set_eq]
  exact_mod_cast hc
end Formalism.UG.P
