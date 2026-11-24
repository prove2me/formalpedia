-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.secondChern_eq_double_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:47.419108+00:00
-- url     : https://prove2.me/submissions/b9eae10d-ddce-4c60-891c-66d7edaa00ce

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_asym_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_zsmul_eq_csmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_min_add_max
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
theorem _root_.solution (w : ℂ) (y : Fin t → A) (x : Fin t → ℂ) (η : Fin t → A) (ξ : Fin t → ℂ) :
    ch2 E w y x η ξ = ∑ q, ∑ p, (ξ q * x p) • ∑ a, ∑ c, η a * y c * nS E a q c p w := by
  set U : Fin t → Fin t → Fin t → Fin t → Fin t → Fin t → Fin t → Fin t → A := fun a b c d i i' j j' =>
    ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
      ((ξ b • η a) * (x d • y c) * qminor E (skip2 i i') (skip2 j j') w) with hU
  have s1 : ch2 E w y x η ξ = ∑ i, ∑ i', (if i < i' then
      (∑ j, ∑ j', if j < j' then U i i' j j' i i' j j' - U i i' j' j i i' j j' else 0) -
      (∑ j, ∑ j', if j < j' then U i' i j j' i i' j j' - U i' i j' j i i' j j' else 0) else 0) := by
    unfold ch2
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun i' _ => ?_
    by_cases h : i < i'
    · rw [if_pos h, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j' _ => ?_
      by_cases h' : j < j'
      · rw [if_pos ⟨h, h'⟩, if_pos h', if_pos h']
        simp only [hU, sub_mul, mul_sub, smul_sub]
        abel
      · rw [if_neg (fun hh => h' hh.2), if_neg h', if_neg h', sub_zero]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
      rw [if_neg (fun hh => h hh.1)]
  rw [s1, asym_sum (fun a b i i' => ∑ j, ∑ j', if j < j' then U a b j j' i i' j j' - U a b j' j i i' j j' else 0)]
  have s2 : ∀ a b i i', (∑ j, ∑ j', if j < j' then U a b j j' i i' j j' - U a b j' j i i' j j' else 0) =
      ∑ c, ∑ d, if c = d then 0 else eps c d • U a b c d i i' (min c d) (max c d) := fun a b i i' =>
    asym_sum (fun c d j j' => U a b c d i i' j j')
  simp_rw [s2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have s3 : ∀ a : Fin t, (if a = b then (0 : A) else eps a b • ∑ c, ∑ d, if c = d then 0 else
      eps c d • U a b c d (min a b) (max a b) (min c d) (max c d)) =
      ∑ d, ∑ c, (ξ b * x d) • (η a * y c * nS E a b c d w) := by
    intro a
    rw [Finset.sum_comm]
    by_cases hab : a = b
    · rw [if_pos hab]
      symm
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
      rw [nS, if_pos (Or.inl hab), mul_zero, smul_zero]
    · rw [if_neg hab, Finset.smul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hcd : c = d
      · rw [if_pos hcd, nS, if_pos (Or.inr hcd), mul_zero, smul_zero, smul_zero]
      · rw [if_neg hcd, nS, if_neg (by tauto)]
        simp only [hU]
        rw [show ((min a b : Fin t) : ℕ) + ((max a b : Fin t) : ℕ) + ((min c d : Fin t) : ℕ) + ((max c d : Fin t) : ℕ) =
          (a : ℕ) + (b : ℕ) + (c : ℕ) + (d : ℕ) by
            have h1 := min_add_max a b
            have h2 := min_add_max c d
            omega]
        simp only [zsmul_eq_csmul, smul_mul_assoc, mul_smul_comm, smul_smul]
        congr 1
        ring
  rw [Finset.sum_congr rfl fun a _ => s3 a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
