-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.omega_clauses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:04:04.360802+00:00
-- url     : https://prove2.me/submissions/764b3242-b3a4-470a-b113-7db0a8f03703

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MlabNotMemYset
import Theorems.Thm_Formalism_MainNotions_PlaneGram_linMap_eq_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mlab_notMem_Yset
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_Pj_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_good_Pj
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Dm_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_kapD_ge_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mlab_notMem_chainSet
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_dg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_zero_iff_Integral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_two_le_p
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_p_pow
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero_iff


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
theorem _root_.solution (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hPj : (∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a))) ∧
      (∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1))) ∧
      (∀ Z (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) (Pj Z)) ∧
      (∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1)) ∧
      (∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ) Z, vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) θ (Pj Z)))
    (gp gm : D.EM → K) (hgp : ∀ ζ, 0 ≤ v (gp ζ)) (hgm : ∀ ζ, 0 ≤ v (gm ζ))
    (hcost : ∀ S : Finset D.ML, (∀ t, D.mlab t ∉ S) → ∀ (θ : ℝ) (Z : MvPolynomial (D.ML × Fin D.r) K),
        vala D.msg S θ Z → vala D.msg S (θ - 12 * D.c) (dg gp Z) ∧ vala D.msg S (θ - 12 * D.c) (dg gm Z)) :
    ((⌈D.Dm p C0 + D.kapD p / 2⌉₊ : ℕ) : ℝ) ≤ D.Dm p C0 + D.kapD p / 2 + 1 ∧
    (∀ Z, Integral v Z → D.Good p Z →
      Integral v (((p : K) ^ ⌈D.Dm p C0 + D.kapD p / 2⌉₊) • dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → D.Good p (dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (i : Fin (D.nch j)),
      vala D.msg (D.chainSet j i) (D.th j i - D.sl j i - 12 * D.c) (dg gm (Pj (dg gp Z)))) ∧
    (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ), m.val + 2 ≤ D.r →
      vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) (θ - 24 * D.c) (dg gm (Pj (dg gp Z)))) := by
  obtain ⟨hP1, hP2, hP3, -, hP5⟩ := hPj
  have hp : 2 ≤ p := two_le_p hD
  have hr : 1 ≤ D.r := hV.1
  have hJ : 1 ≤ D.J := hV.2.1
  have hkap := D.kapD_ge_one hp hr hJ
  have hDm := D.Dm_nonneg hp hr h1
  have hpos : 0 ≤ D.Dm p C0 + D.kapD p / 2 := by linarith
  refine ⟨(Nat.ceil_lt_add_one hpos).le, ?_, ?_, ?_, ?_⟩
  · intro Z hZi hZg
    rw [← cge_zero_iff_Integral]
    have hY : cge v 0 (dg gp Z) := by
      have := cge_dg v (a := 0) (b := 0) (f := gp) (fun ζ => (vge_zero_iff v _).mpr (hgp ζ))
        ((cge_zero_iff_Integral v Z).mpr hZi)
      simpa using this
    have hYg : D.Good p (dg gp Z) := TwistData.Good.dg D hZg gp
    have hPY : cge v (-(D.Dm p C0 + D.kapD p / 2)) (Pj (dg gp Z)) := by
      rw [linMap_eq_sum Pj (dg gp Z)]
      refine cge_sum v _ _ fun ζ hζ => ?_
      have := cge_smul v (hY ζ) (cge_Pj_monomial hD D hr Pj hP1 hP2 ζ (hYg ζ hζ))
      simpa using this
    have hG : cge v (-(D.Dm p C0 + D.kapD p / 2)) (dg gm (Pj (dg gp Z))) := by
      have := cge_dg v (a := 0) (f := gm) (fun ζ => (vge_zero_iff v _).mpr (hgm ζ)) hPY
      simpa using this
    have := cge_smul v (vge_p_pow hD ⌈D.Dm p C0 + D.kapD p / 2⌉₊) hG
    refine cge_mono v ?_ this
    have := Nat.le_ceil (D.Dm p C0 + D.kapD p / 2)
    linarith
  · intro Z hZg
    exact TwistData.Good.dg D (good_Pj D Pj hP1 (TwistData.Good.dg D hZg gp)) gm
  · intro Z _ j i
    exact (hcost (D.chainSet j i) (D.mlab_notMem_chainSet j i) _ _ (hP3 (dg gp Z) j i)).2
  · intro Z _ j m θ _ hZ
    have a1 := (hcost (D.Yset j m) (D.mlab_notMem_Yset j m) θ Z hZ).1
    have a2 := hP5 j m _ _ a1
    have a3 := (hcost (D.Yset j m) (D.mlab_notMem_Yset j m) _ _ a2).2
    exact vala_mono (by linarith) a3
end Formalism.MainNotions.PlaneGram
