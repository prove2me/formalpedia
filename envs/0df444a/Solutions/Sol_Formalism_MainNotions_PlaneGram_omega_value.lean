-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.omega_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:10:19.332437+00:00
-- url     : https://prove2.me/submissions/065f50d5-7a11-42f6-bbb0-e8fffed8af29

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MlabNotMemYset
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_OmegaValue
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Dm_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_v_gaP
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_value_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_vge_Lam_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_smul_right
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_sum_right
import Theorems.Thm_Formalism_MainNotions_PlaneGram_gaAct_eq_dg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_rat_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero_iff
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_lg_nonneg__7f797abb6a20
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_add__0d0ebe1b2fad
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_mono__13f616ce561b
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_mul__293e99e62721
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_sum__98181df79b27


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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p) (hH : D.HypH p 13)
    (hE : StepE K v p) {F : MvPolynomial (D.OL × Fin D.r) K} (hF : D.InXX p F) (hF0 : bge v 0 F)
    {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K} {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K}
    (hdig : D.DigOK v p cst gam)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → D.SameBlockAlt ζ ζ')
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (hP4 : ∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1))
    (gp gm : D.EM → K) (hgp0 : ∀ ζ, 0 ≤ v (gp ζ))
    (happ : ∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gp ζ - D.gaP p gam ζ) ∧
        ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹))
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZi : Integral v Z) (hZg : D.Good p Z) :
    vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (D.abelian₂ p F (dg gm (Pj (dg gp Z))) - D.abelian₂ p F Z) := by
  have key : ∀ W, D.abelian₂ p F W = fock F (dg D.ga (D.ph p W)) := fun W => by
    simp only [TwistData.abelian₂, gaAct_eq_dg]
  have hLsum : ∀ (s : Finset D.EM) (f : D.EM → MvPolynomial (D.ML × Fin D.r) K),
      D.abelian₂ p F (∑ i ∈ s, f i) = ∑ i ∈ s, D.abelian₂ p F (f i) := by
    intro s f
    simp only [key, map_sum, fock_sum_right]
  have hLsmul : ∀ (c : K) (W : MvPolynomial (D.ML × Fin D.r) K), D.abelian₂ p F (c • W) = c * D.abelian₂ p F W := by
    intro c W
    simp only [key, map_smul, fock_smul_right]
  have hmon : ∀ (g : D.EM → K) (ζ : D.EM), dg g (monomial ζ (1 : K)) = g ζ • monomial ζ (1 : K) := by
    intro g ζ
    rw [dg_monomial, MvPolynomial.smul_monomial, smul_eq_mul]
  have hZ : Z = ∑ ζ ∈ Z.support, Z.coeff ζ • monomial ζ (1 : K) := by
    conv_lhs => rw [Z.as_sum]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hp2 : 2 ≤ p := by have := hD.five_le; omega
  have hr1 : 1 ≤ D.r := hV.1
  have hkap : 0 ≤ D.kapD p := by
    unfold TwistData.kapD kap
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (lg_nonneg' hp2 hr1 _)
  have hDm : 0 ≤ D.Dm p C0 := TwistData.Dm_nonneg (D := D) hp2 hr1 h1
  rw [hZ, map_sum (dg gp), map_sum Pj, map_sum (dg gm), hLsum, hLsum, ← Finset.sum_sub_distrib]
  simp only [map_smul, hLsmul]
  apply vge_sum'
  intro ζ hζ
  rw [← mul_sub]
  have hgood : D.GoodE p ζ := hZg ζ hζ
  have hlow : D.LabLowE p ζ := hgood.1
  have h1' : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) =
      gp ζ * D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) := by
    rw [hmon, map_smul, map_smul, hLsmul]
  have h2' : D.abelian₂ p F (dg gm (monomial ζ (1 : K))) = gm ζ * D.abelian₂ p F (monomial ζ (1 : K)) := by
    rw [hmon, hLsmul]
  have hexp : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) - D.abelian₂ p F (monomial ζ (1 : K)) =
      gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K)))) +
        (gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K)) := by
    rw [h1', h2']
    ring
  rw [hexp]
  have hval := TwistData.value_monomial (D := D) hD h1 hV hH hE hF hF0 hdig Pj hP1 hP2 hP4 gm
    (fun ζ h => (happ ζ h).2) hgood
  have hZζ : vge v 0 (Z.coeff ζ) := (vge_zero_iff v _).mpr (hZi ζ)
  have hgp' : vge v 0 (gp ζ) := (vge_zero_iff v _).mpr (hgp0 ζ)
  have t1 : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K))))) := by
    have := vge_mul' v hgp' hval
    simpa using this
  have hgaP : v (D.gaP p gam ζ) = 0 := TwistData.v_gaP (D := D) hV hdig hlow
  have hg0 : D.gaP p gam ζ ≠ 0 := by
    intro h
    rw [h] at hgaP
    simp at hgaP
  have hgaP' : vge v 0 (D.gaP p gam ζ) := (vge_zero_iff v _).mpr (le_of_eq hgaP.symm)
  have hc1 : vge v (D.c : ℝ) (gp ζ - D.gaP p gam ζ) := by
    have := (vge_rat_iff (v := v) (D.c : ℚ) (gp ζ - D.gaP p gam ζ)).mpr (by exact_mod_cast (happ ζ hlow).1)
    simpa using this
  have hc2 : vge v (D.c : ℝ) (gm ζ - (D.gaP p gam ζ)⁻¹) := by
    have := (vge_rat_iff (v := v) (D.c : ℚ) (gm ζ - (D.gaP p gam ζ)⁻¹)).mpr (by exact_mod_cast (happ ζ hlow).2)
    simpa using this
  have hgm' : vge v 0 (gm ζ) := by
    have h3 : gm ζ = (gm ζ - (D.gaP p gam ζ)⁻¹) + (D.gaP p gam ζ)⁻¹ := by ring
    rw [h3]
    refine vge_add' v (vge_mono' v (by positivity) hc2) ?_
    rw [vge_zero_iff v, AddValuation.map_inv, hgaP, neg_zero]
  have hsplit : gp ζ * gm ζ - 1 =
      (gp ζ - D.gaP p gam ζ) * gm ζ + D.gaP p gam ζ * (gm ζ - (D.gaP p gam ζ)⁻¹) := by
    rw [mul_sub (D.gaP p gam ζ), mul_inv_cancel₀ hg0]
    ring
  have t2 : vge v (D.c : ℝ) (gp ζ * gm ζ - 1) := by
    rw [hsplit]
    refine vge_add' v ?_ ?_
    · simpa using vge_mul' v hc1 hgm'
    · simpa using vge_mul' v hgaP' hc2
  have hΛ := TwistData.vge_Lam_monomial (D := D) hD hV hF0 hgood
  have t3 := vge_mul' v t2 hΛ
  have t3' : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      ((gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K))) := vge_mono' v (by linarith) t3
  simpa using vge_mul' v hZζ (vge_add' v t1 t3')
end Formalism.MainNotions.PlaneGram
