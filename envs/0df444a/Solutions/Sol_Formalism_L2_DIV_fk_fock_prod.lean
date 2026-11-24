-- Prove2me | solution 1 for Formalism.L2.DIV.fk_fock_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:20:28.957194+00:00
-- url     : https://prove2.me/submissions/67643ce5-fe5c-4252-ab96-9650c650b860

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_pderiv_blockEmb_ne
import Theorems.Thm_Formalism_L2_DIV_fk_fock_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_DIV_fockL_C_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K] {ι : Type} {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (s : Finset ι) (f g : ι → MvPolynomial (Fin n × Fin n) K) :
    fockL (∏ τ ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) (∏ τ ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ (g τ)) =
      ∏ τ ∈ s, fockL (f τ) (g τ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [← C_1, fockL_C_left]
    simp
  | insert τ s hτ ih =>
    have hz : ∀ (h : ι → MvPolynomial (Fin n × Fin n) K) (v : Fin n × Fin n),
        pderiv (τ, v) (∏ τ' ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ' (h τ')) = 0 := by
      intro h v
      refine Finset.prod_induction _ (fun P => pderiv (τ, v) P = 0) ?_ ?_ ?_
      · intro a b ha hb
        rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      · exact (pderiv (τ, v)).map_one_eq_zero
      · intro τ' hτ'
        exact fk_pderiv_blockEmb_ne (fun e : τ = τ' => hτ (by rw [e]; exact hτ')) v _
    rw [Finset.prod_insert hτ, Finset.prod_insert hτ, Finset.prod_insert hτ, fk_fock_mul τ _ _ (hz f) (hz g), ih]
end Formalism.L2.DIV
