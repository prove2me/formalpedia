-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.value_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:04:03.447785+00:00
-- url     : https://prove2.me/submissions/da78b48f-90ac-4b7b-aef9-e39309d01d57

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_coeff_digitPart_eIn
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_v_gaP
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ne_zero_of_v_eq_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Lam_monomial_blk
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_vge_coeff_GM
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Lam_dg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ldeg_tpE
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_msg_of_eOut_ne_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Dm_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_GoodE_good_exponent_same_block
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_SameBlockAlt_refl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_kappa_constant_same_block
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_label_function_same_block
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_output_exponent_same_block
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_tangent_exponent_same_block
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_vge_kapC
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_wt_lower
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_hcomp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_add_eIn
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_ne_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_eq_sum_right
import Theorems.Thm_Formalism_MainNotions_PlaneGram_hcomp_mem_PolK
import Theorems.Thm_Formalism_MainNotions_PlaneGram_two_le_p
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_monomial_nonneg_of_vec
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_hcomp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mul_left_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_natCast_bound
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_sub
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_unit
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_vN
import Theorems.Thm_UpperTheory_Reformulated_B_Qh31_vge_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution {C0 : ℝ} (hD : DVRHyp v p) (h1 : 1 ≤ C0) (hV : D.Valid v p) (hH : D.HypH p 13)
    (hE : StepE K v p) {F : MvPolynomial (D.OL × Fin D.r) K} (hF : D.InXX p F) (hF0 : bge v 0 F)
    {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K} {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K}
    (hdig : D.DigOK v p cst gam)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → D.SameBlockAlt ζ ζ')
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (hP4 : ∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1))
    (gm : D.EM → K)
    (hgm : ∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹))
    {ζ : D.EM} (hζ : D.GoodE p ζ) :
    vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (D.abelian₂ p F (dg gm (Pj (monomial ζ 1))) - D.abelian₂ p F (dg gm (monomial ζ 1))) := by
  classical
  have hDm := D.Dm_nonneg (two_le_p hD) hV.1 h1
  obtain ⟨Q0, E', hQ, hQ0, hE'⟩ := hE hD D hV hH F hF hF0 (D.tpE ζ) (fun b a => by simp [tpE])
    (fun t => by rw [ldeg_tpE]; exact hζ.2.2.2.2 t) (D.labF ζ)
  set μ := eOut D.outP ζ with hμ
  set A := hcomp (fun i => ldeg ζ i) (monomial μ 1 * Q0) with hA
  set κ := D.kapC cst ζ with hκ
  set e : D.EM → K := fun ζ' =>
    gm ζ' * D.gaP p gam ζ' * (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ') - A.coeff ζ' with he

  have key : ∀ W : MvPolynomial (D.ML × Fin D.r) K, (∀ ζ' ∈ W.support, D.SameBlockAlt ζ ζ') →
      D.abelian₂ p F (dg gm W) = κ * fock A W + ∑ ζ' ∈ W.support, κ * (W.coeff ζ' * e ζ' * (fact ζ' : K)) := by
    intro W hW
    rw [Lam_dg, fock_eq_sum_right, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ζ' hζ' => ?_
    have hb := hW ζ' hζ'
    rw [D.Lam_monomial_blk hV hdig F (hζ.good_exponent_same_block D hb).1, D.tangent_exponent_same_block hb, D.kappa_constant_same_block cst hb, he]
    ring

  have herr : ∀ ζ', D.SameBlockAlt ζ ζ' → vge v (D.c - D.n0 v) (e ζ') := by
    intro ζ' hb
    have hl := (hζ.good_exponent_same_block D hb).1
    have c1 : A.coeff ζ' = Q0.coeff (eIn D.outP ζ') := by
      rw [hA, coeff_hcomp, if_pos hb.1]
      conv_lhs => rw [← eOut_add_eIn D.outP ζ', D.output_exponent_same_block hb]
      rw [coeff_monomial_mul, one_mul]
    have c2 : (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ') =
        Q0.coeff (eIn D.outP ζ') + E'.coeff (eIn D.outP ζ') := by
      rw [← D.coeff_digitPart_eIn p hl, D.label_function_same_block hb, ← coeff_add, ← hQ]; rfl
    have hu := D.v_gaP hV hdig hl
    have hu0 := ne_zero_of_v_eq_zero hu
    have c3 : e ζ' = (gm ζ' - (D.gaP p gam ζ')⁻¹) * D.gaP p gam ζ' *
        (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ') + E'.coeff (eIn D.outP ζ') := by
      rw [he]; simp only; rw [c1, sub_mul, inv_mul_cancel₀ hu0]
      have := c2
      linear_combination this
    rw [c3]
    have b1 : vge v (D.c : ℝ) (gm ζ' - (D.gaP p gam ζ')⁻¹) := (vge_natCast_bound v _ _).mpr (hgm ζ' hl)
    have b2 := (vge_unit v hu).1
    have b3 : vge v (-D.n0 v) ((D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ')) := by
      rw [← D.tangent_exponent_same_block hb]; exact D.vge_coeff_GM hD hV hF.1 hF0 ζ'
    refine vge_add v ?_ (hE' _)
    exact vge_mono v (by linarith) (vge_mul v (vge_mul v b1 b2) b3)

  have hterm : ∀ ζ', D.SameBlockAlt ζ ζ' → ∀ w : K,
      vge v (vN v (fact ζ) / 2 - D.Dm p C0 - vN v (fact ζ') / 2) w →
      vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0) (κ * (w * e ζ' * (fact ζ' : K))) := by
    intro ζ' hb w hw
    have hg' := hζ.good_exponent_same_block D hb
    have k1 := D.vge_kapC hD hdig hg'.1
    rw [D.kappa_constant_same_block cst hb] at k1
    have k2 := D.vge_kapC hD hdig hζ.1
    have w1 := D.wt_lower hD hV.1 hg'
    have w2 := D.wt_lower hD hV.1 hζ
    have f1 := vge_vN hD (fact_ne_zero ζ')
    have t1 := vge_mul v (vge_mul v hw (herr ζ' hb)) f1
    rcases le_total (vN v (fact ζ')) (vN v (fact ζ)) with hle | hle
    · exact vge_mono v (by linarith) (vge_mul v k1 t1)
    · exact vge_mono v (by linarith) (vge_mul v k2 t1)
  have hs1 : ∀ ζ' ∈ (Pj (monomial ζ 1)).support, D.SameBlockAlt ζ ζ' := fun ζ' h => hP1 ζ ζ' h
  have hs2 : ∀ ζ' ∈ (monomial ζ (1 : K)).support, D.SameBlockAlt ζ ζ' := by
    intro ζ' h
    have := support_monomial_subset h
    rw [Finset.mem_singleton] at this
    rw [this]; exact TwistData.SameBlockAlt.refl D ζ
  have hAv : ∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A :=
    fun j i => vala_hcomp _ (vala_mul_left_nonneg
      (valS_monomial_nonneg_of_vec μ 1 (D.msg_of_eOut_ne_zero ζ)) (hQ0 j i))
  rw [key _ hs1, key _ hs2, hP4 A ζ (hcomp_mem_PolK _ _) hAv, add_sub_add_left_eq_sub]
  refine vge_sub v (vge_sum v _ _ fun ζ' h => hterm ζ' (hs1 ζ' h) _ (hP2 ζ hζ ζ'))
    (vge_sum v _ _ fun ζ' h => hterm ζ' (hs2 ζ' h) _ ?_)
  have := support_monomial_subset h
  rw [Finset.mem_singleton] at this
  rw [this, coeff_monomial, if_pos rfl]
  exact vge_mono v (by linarith) (vge_one v)
end Formalism.MainNotions.PlaneGram.TwistData
