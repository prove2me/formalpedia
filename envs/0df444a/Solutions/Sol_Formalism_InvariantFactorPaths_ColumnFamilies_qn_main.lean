-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:58:30.447746+00:00
-- url     : https://prove2.me/submissions/e9aefc76-a4ad-40ad-ae54-4c5810aced95

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnInterlacedLowerTri
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnEvalMap
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_eval_map
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_InZ_UZ
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_InZ_span
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylIntRat
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_divPowE
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_map
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_colHom
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_eval_eq_coeff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_lowerTriIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_tri
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_transposeVariables_involutive
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_otherWts__b7efafda174b
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_ColumnFamilies_qn_otherWts_coeff__f1290125d7fe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) {ι : Type}
    (P : ι → MvPolynomial (Fin n × Fin n) ℤ) (i0 : ι)
    (h1 : ∀ i, transposeVariables ℤ n (P i) ∈ dualWeyl ℤ n n ν)
    (h2 : dualWeyl ℤ n n ν ≤ Submodule.span ℤ (Set.range fun i => transposeVariables ℤ n (P i)))
    (h3 : eval (idFrame ℤ n n) (transposeVariables ℤ n (P i0)) = 1) :
    (Submodule.span ℤ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) :
        Set (MvPolynomial (Fin n × Fin n) ℚ)) =
      {x | x ∈ Submodule.span ℚ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) ∧
        x ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ))
          (map (Int.castRingHom ℚ) (P i0))} := by
  classical
  set v := map (Int.castRingHom ℚ) (P i0) with hv
  have hTv : transposeVariables ℚ n v = map (Int.castRingHom ℚ) (transposeVariables ℤ n (P i0)) := qn_T_map n (P i0)
  have hTvmem : transposeVariables ℚ n v ∈ dualWeyl ℚ n n ν := by
    rw [hTv]; exact dualWeylMap ℤ ℚ _ n n ν _ (h1 i0)
  have hTvev : eval (idFrame ℚ n n) (transposeVariables ℚ n v) = 1 := by
    rw [hTv, qn_eval_map, h3, Int.cast_one]
  ext x
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨Submodule.span_le_restrictScalars ℤ ℚ _ hx, ?_⟩
    intro u hu
    obtain ⟨Y, hY, hy⟩ := qn_InZ_UZ n ν u hu x (qn_InZ_span n ν P h1 x hx)
    refine ⟨eval (idFrame ℤ n n) Y, ?_⟩
    apply qn_mem_otherWts'
    have hYQ : transposeVariables ℚ n (u x) ∈ dualWeyl ℚ n n ν := by
      rw [hy]; exact dualWeylMap ℤ ℚ _ n n ν _ hY
    rw [map_sub, map_smul, map_sub, map_smul, qn_comp n ν hν _ hYQ, qn_comp n ν hν _ hTvmem, hTvev, hy,
      qn_eval_map, one_smul, eq_intCast, sub_self]
  · rintro ⟨hxQ, hxN⟩
    have hxD : transposeVariables ℚ n x ∈ dualWeyl ℚ n n ν := by
      have hle : Submodule.span ℚ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) ≤
          (dualWeyl ℚ n n ν).comap (transposeVariables ℚ n).toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        show transposeVariables ℚ n (map (Int.castRingHom ℚ) (P i)) ∈ dualWeyl ℚ n n ν
        rw [qn_T_map]
        exact dualWeylMap ℤ ℚ _ n n ν _ (h1 i)
      exact hle hxQ
    set W : Set (MvPolynomial (Fin n × Fin n) ℚ) :=
      {F | ∃ y, F = transposeVariables ℚ n y ∧ transposeVariables ℚ n y ∈ dualWeyl ℚ n n ν ∧
        y ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ)) v} with hWdef
    have hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W := by
      rintro F ⟨y, rfl, hyD, hyN⟩ a b k hab
      refine ⟨divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k y, (qn_T_divPowE n a b hab k y).symm, ?_, ?_⟩
      · rw [qn_T_divPowE n a b hab]
        exact rowDivStable ℚ n n ν a b k _ hyD
      · intro u hu
        have hg : divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k ∈
            UZmon (glOps ℚ n (rowLetters n) Set.univ) :=
          Submonoid.subset_closure (Or.inl ⟨a, b, k, hab, rfl⟩)
        exact hyN (u * divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k) (Submonoid.mul_mem _ hu hg)
    have hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z := by
      rintro F ⟨y, rfl, hyD, hyN⟩
      obtain ⟨c, hc⟩ := hyN 1 (Submonoid.one_mem _)
      refine ⟨c, ?_⟩
      have h := qn_otherWts_coeff' n ν _ hc
      rw [Module.End.one_apply, map_sub, map_smul, coeff_sub, coeff_smul,
        ← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ hyD), ← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ hTvmem),
        hTvev, smul_eq_mul, mul_one, eq_intCast, sub_eq_zero] at h
      exact h
    have hcol : ∀ F ∈ W, IsWeightedHomogeneous (colW n n) F ν := by
      rintro F ⟨y, rfl, hyD, _⟩
      exact qn_colHom ℚ n ν _ hyD
    have htri := qn_tri n ν W hW hev hcol (transposeVariables ℚ n x) ⟨x, rfl, hxD, hxN⟩
    obtain ⟨Q', hQ'⟩ := qn_lowerTriIntegral n n ν (transposeVariables ℚ n x) hxD htri
    have hQ'' : transposeVariables ℚ n x = map (Int.castRingHom ℚ) Q' := hQ'
    have hQmem : Q' ∈ dualWeyl ℤ n n ν := (dualWeylIntRat n n ν Q').mpr (hQ'' ▸ hxD)
    have hQs := h2 hQmem
    set φ : MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℚ :=
      (intQ n n).comp (transposeVariables ℤ n).toLinearMap with hφ
    have hφx : φ Q' = x := by
      show map (Int.castRingHom ℚ) (transposeVariables ℤ n Q') = x
      rw [← qn_T_map, ← hQ'', transposeVariables_involutive]
    have hx := Submodule.mem_map_of_mem (f := φ) hQs
    rw [Submodule.map_span, hφx] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    show _ = map (Int.castRingHom ℚ) (transposeVariables ℤ n (transposeVariables ℤ n (P i)))
    rw [transposeVariables_involutive]
end Formalism.InvariantFactorPaths.ColumnFamilies
