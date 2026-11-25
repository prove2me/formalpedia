-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.stepP_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:10:23.641074+00:00
-- url     : https://prove2.me/submissions/883512f4-e941-4800-8f7a-c5286a11576b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_lg_mono__9d5245f1fc9a
import Theorems.Thm_Formalism_MainNotions_PlaneGram_monomial_mem_PolK
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mlab_notMem_chainSet
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mtp_notMem_chainSet
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_chainSet_pair
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_chainSet_Yset
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_sum_ldeg_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Aset_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Aset_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_hcomp_mem_PolK
import Theorems.Thm_Formalism_MainNotions_PlaneGram_mem_PolK_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_prodProj
import Theorems.Thm_Formalism_MainNotions_PlaneGram_prodProj_entries
import Theorems.Thm_Formalism_MainNotions_PlaneGram_sum_hcomp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_hcomp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_iff_Aset


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
variable {K : Type} [Field K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ) (C0 : ℝ) (h1 : 1 ≤ C0)
    (hP : PROJ K v p C0) : StepP K v p C0 := by
  intro hD D hV
  obtain ⟨hr, hJ, hc, hch, hnest, hthl, hga⟩ := hV
  haveI : NeZero D.r := ⟨hr.ne'⟩
  have hp0 : 0 < p := hD.prime.pos
  have hp2 : 2 ≤ p := by have := hD.five_le; omega

  let Sx : (Σ j : Fin D.J, Fin (D.nch j)) → Finset D.ML := fun x => D.chainSet x.1 x.2
  let thx : (Σ j : Fin D.J, Fin (D.nch j)) → ℤ := fun x => ⌈D.th x.1 x.2 - D.sl x.1 x.2⌉
  have hpair : ∀ x ∈ (Finset.univ : Finset (Σ j : Fin D.J, Fin (D.nch j))), ∀ y ∈ Finset.univ,
      Sx x ⊆ Sx y ∨ Sx y ⊆ Sx x ∨ Disjoint (Sx x) (Sx y) :=
    fun x _ y _ => D.chainSet_pair hch hnest x y

  have hex := fun d : D.ML → ℕ =>
    prodProj (L := D.ML) (sg := D.msg) (r := D.r) (d := d) hP hD Finset.univ Sx thx hpair
  choose Pr h1 h2 h3 h4 h5 h6 using hex
  obtain ⟨Pj, hPj⟩ : ∃ Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K,
      ∀ ζ : D.EM, Pj (monomial ζ 1) = Pr (fun i => ldeg ζ i) (monomial ζ 1) := by
    refine ⟨(MvPolynomial.basisMonomials (D.ML × Fin D.r) K).constr K
      (fun ζ => Pr (fun i => ldeg ζ i) (monomial ζ 1)), fun ζ => ?_⟩
    have e := (MvPolynomial.basisMonomials (D.ML × Fin D.r) K).constr_basis K
      (fun ζ => Pr (fun i => ldeg ζ i) (monomial ζ 1)) ζ
    rw [MvPolynomial.coe_basisMonomials] at e
    exact e
  have hmono : ∀ (ζ : D.EM) (c : K), monomial ζ c = c • (monomial ζ 1 : MvPolynomial (D.ML × Fin D.r) K) := by
    intro ζ c
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hlin : ∀ Z : MvPolynomial (D.ML × Fin D.r) K,
      Pj Z = ∑ ζ ∈ Z.support, Z.coeff ζ • Pr (fun i => ldeg ζ i) (monomial ζ 1) := by
    intro Z
    conv_lhs => rw [Z.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    rw [hmono, map_smul, hPj]
  have hhom : ∀ (d : D.ML → ℕ), ∀ F ∈ PolK K D.r d, Pj F = Pr d F := by
    intro d F hF
    rw [hlin]
    conv_rhs => rw [F.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun ζ hζ => ?_)
    have hd : (fun i => ldeg ζ i) = d := funext ((mem_PolK_iff d F).1 hF ζ hζ)
    rw [hd, hmono ζ (F.coeff ζ), map_smul]
  refine ⟨Pj, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ ζ' hmem
    rw [hPj] at hmem
    obtain ⟨hdeg, hfix⟩ := prodProj_entries D.msg (fun i => ldeg ζ i) Finset.univ Sx
      (Pr (fun i => ldeg ζ i)) (h1 _) (h6 _) ζ (fun k => rfl) ζ' hmem
    exact ⟨hdeg, fun t a => hfix _ rfl (fun x _ => D.mlab_notMem_chainSet x.1 x.2 t) a,
      fun t a => hfix _ rfl (fun x _ => D.mtp_notMem_chainSet x.1 x.2 t) a⟩
  · intro ζ hG
    have hbm : bge v (vN v (fact ζ) / 2) (monomial ζ (1 : K)) := by
      classical
      intro α
      rw [MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst h
        simp [vge, vR, AddValuation.map_one]
      · simp [vge, vR, AddValuation.map_zero]
    have hb := h4 (fun i => ldeg ζ i) (monomial ζ 1) (monomial_mem_PolK ζ 1) _ hbm
    rw [hPj]
    refine bge_mono (hab := ?_) (h := hb)
    have hcard : ((Finset.univ : Finset (Σ j : Fin D.J, Fin (D.nch j))).card : ℝ)
        = ∑ j, (D.nch j : ℝ) := by
      rw [Finset.card_univ, Fintype.card_sigma]
      simp [Fintype.card_fin]
    have hlg : lg p D.r (2 * ∑ i, ldeg ζ i) ≤ lg p D.r (2 * D.totDeg) :=
      lg_mono' hp2 hr (by have := D.sum_ldeg_le p hp0 ζ hG; omega)
    have hDm : D.Dm p C0 = (∑ j, (D.nch j : ℝ)) * ((D.r : ℝ) ^ 2 * lg p D.r (2 * D.totDeg)) := by
      unfold TwistData.Dm TwistData.eC
      rw [Finset.sum_mul]
    have hnn : (0 : ℝ) ≤ ∑ j, (D.nch j : ℝ) := Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)
    have hm : (∑ j, (D.nch j : ℝ)) * ((D.r : ℝ) ^ 2 * lg p D.r (2 * ∑ i, ldeg ζ i))
        ≤ (∑ j, (D.nch j : ℝ)) * ((D.r : ℝ) ^ 2 * lg p D.r (2 * D.totDeg)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlg (sq_nonneg _)) hnn
    rw [hcard, hDm]
    linarith
  · intro Z j i
    rw [vala_iff_Aset, hlin]
    apply Aset_sum
    intro ζ _
    apply Aset_smul
    exact h2 _ _ (monomial_mem_PolK ζ 1) ⟨j, i⟩ (Finset.mem_univ _)
  · intro A ζ hA hvA
    rw [hPj]
    exact h3 _ A hA (fun x _ => (vala_iff_Aset _ _ _ _).1 (hvA x.1 x.2)) _ (monomial_mem_PolK ζ 1)
  · intro j m θ Z hZ
    have hsplit : Pj Z = ∑ d ∈ Z.support.image (fun α i => ldeg α i), Pr d (hcomp d Z) := by
      conv_lhs => rw [sum_hcomp Z]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun d _ => hhom d _ (hcomp_mem_PolK d Z))
    rw [vala_iff_Aset, hsplit]
    apply Aset_sum
    intro d _
    exact h5 d (D.Yset j m) ⌈θ⌉ (fun x _ => D.chainSet_Yset hch x.1 x.2 j m) _ (hcomp_mem_PolK d Z)
      ((vala_iff_Aset _ _ _ _).1 (vala_hcomp d hZ))
end Formalism.MainNotions.PlaneGram
