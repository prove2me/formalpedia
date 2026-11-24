-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.invGood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:42.023246+00:00
-- url     : https://prove2.me/submissions/4c772422-ac2b-42b0-b6b8-bb413a807900

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
import Theorems.Thm_Formalism_NG_BlockDetAlt_isUnit_det_of_const

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
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    {A : Matrix d d (PowerSeries (X' → FractionRing O))} (hA : A ∈ goodM R')
    (hc : (PowerSeries.constantCoeff).mapMatrix A = 1) : A⁻¹ ∈ goodM R' := by
  have hAB : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_det_of_const A hc)
  have h0 : coefMat 0 A = 1 := by
    ext x' i j
    have h1 := congrArg (fun M => M i j x') hc
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    simp only [coefMat, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  show ∀ n, coefMat n A⁻¹ ∈ R'
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have e := congrArg (coefMat n) hAB
    rw [coefMat_mul, coefMat_one] at e
    have hmem : ((0 : ℕ), n) ∈ antidiagonal n := by simp
    have hB : coefMat n A⁻¹ = (if n = 0 then 1 else 0) -
        ∑ p ∈ (antidiagonal n).erase (0, n), coefMat p.1 A * coefMat p.2 A⁻¹ := by
      rw [← e, ← Finset.add_sum_erase _ _ hmem, h0, one_mul]
      abel
    rw [hB]
    apply Subalgebra.sub_mem
    · split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · apply Subalgebra.sum_mem
      intro p hp
      rw [Finset.mem_erase] at hp
      have hp2 : p.1 + p.2 = n := by simpa using hp.2
      apply Subalgebra.mul_mem _ (hA p.1) (ih p.2 ?_)
      by_contra hlt
      exact hp.1 (Prod.ext (by simp; omega) (by simp; omega))
end Formalism.NG.BlockDetAlt
