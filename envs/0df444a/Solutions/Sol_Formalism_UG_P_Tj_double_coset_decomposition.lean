-- Prove2me | solution 1 for Formalism.UG.P.Tj_double_coset_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:58:53.395862+00:00
-- url     : https://prove2.me/submissions/e16aee06-e250-4506-a2a8-79625f824fc3

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Theorems.Thm_Formalism_UG_P_tjcosets_arith
import Theorems.Thm_Formalism_UG_P_tjcosets_finite
import Theorems.Thm_Formalism_UG_P_tjcosets_ne_zero
import Theorems.Thm_Formalism_UG_P_tjcosets_hmax
import Theorems.Thm_Formalism_UG_P_tjcosets_card_residue
import Theorems.Thm_Formalism_UG_P_tjcosets_tj_ne_zero
import Theorems.Thm_Formalism_UG_P_tjcosets_ff_count
import Theorems.Thm_Formalism_UG_P_tjcosets_index


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.TjCosets := by
  intro F _ _ v n ϖ hϖO hϖ j hj
  have hϖ0 := tjcosets_ne_zero v ϖ hϖ
  haveI := tjcosets_finite v
  have hmax := tjcosets_hmax v ϖ hϖ
  have hset : {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
      Tj ℤ n (Ov F v) ϖ j x.out ≠ 0} = {x | ∃ a ∈ GLint (Fin n) (Ov F v),
        ∃ b ∈ GLint (Fin n) (Ov F v), x.out = a * tjcosets_dG n j ϖ hϖ0 * b} := by
    ext x
    exact tjcosets_tj_ne_zero _ n j ϖ hϖ0 x.out
  have hC : Nat.card {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
      Tj ℤ n (Ov F v) ϖ j x.out ≠ 0} =
      (tjcosets_par (𝔽 := IsLocalRing.ResidueField (Ov F v)) n j).index := by
    rw [hset]
    exact tjcosets_index (O := Ov F v) n j ϖ hϖO hϖ0 hmax
  letI : Fintype (IsLocalRing.ResidueField (Ov F v)) := Fintype.ofFinite _
  have hcount := tjcosets_ff_count (𝔽 := IsLocalRing.ResidueField (Ov F v)) n j hj
  have hq : Fintype.card (IsLocalRing.ResidueField (Ov F v)) = qV F v := by
    rw [Fintype.card_eq_nat_card]
    exact tjcosets_card_residue v
  have hq2 : 2 ≤ qV F v := by
    rw [← hq]
    exact Fintype.one_lt_card
  rw [hq] at hcount
  rw [hC]
  exact tjcosets_arith (qV F v) n j _ hq2 hj hcount
end Formalism.UG.P
