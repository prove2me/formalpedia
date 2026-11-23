-- Prove2me | solution 1 for Formalism.L2.Col.exists_diagEmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:02.306854+00:00
-- url     : https://prove2.me/submissions/c0cb6a1c-eae9-4a6b-bb40-643ff0cf2f53

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_sub_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution {s : ℕ} (M : GL (Fin (s + 1)) κ) (hc : M ∈ fixCol (s + 1) κ s)
    (hr : ∀ j : Fin (s + 1), j.val < s → (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) (Fin.last s) j = 0) :
    ∃ g : GL (Fin s) κ, diagEmb κ (Nat.le_succ s) g = M ∧
      ∀ i j : Fin s, (g : Matrix (Fin s) (Fin s) κ) i j = (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc j.castSucc := by
  have hcol : ∀ i : Fin (s + 1), (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) :=
    fun i => hc i (Fin.last s) rfl
  have hc' : M⁻¹ ∈ fixCol (s + 1) κ s := Subgroup.inv_mem _ hc
  have hcol' : ∀ i : Fin (s + 1), ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i (Fin.last s) :=
    fun i => hc' i (Fin.last s) rfl
  have hA : ∀ i : Fin s, (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc (Fin.last s) = 0 := by
    intro i; rw [hcol, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  have hA' : ∀ i : Fin s, ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i.castSucc (Fin.last s) = 0 := by
    intro i; rw [hcol', Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  have hmul : (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc *
      ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc = 1 := by
    rw [← Formalism.L2.Col.sub_mul _ _ hA, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.submatrix_one _ (Fin.castSucc_injective s)]
  have hmul' : ((M⁻¹ : GL (Fin (s + 1)) κ) : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc *
      (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc = 1 := by
    rw [← Formalism.L2.Col.sub_mul _ _ hA', ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.submatrix_one _ (Fin.castSucc_injective s)]
  refine ⟨⟨_, _, hmul, hmul'⟩, ?_, fun i j => rfl⟩
  apply Units.ext
  ext i j
  show diagMat s (s + 1) ((M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ).submatrix Fin.castSucc Fin.castSucc) i j = (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) i j
  simp only [diagMat]
  split_ifs with hs
  · rfl
  · have hi2 := i.2
    have hj2 := j.2
    by_cases hj : j.val = s
    · have hjl : j = Fin.last s := Fin.ext hj
      subst hjl
      exact (hcol i).symm
    · have hil : i = Fin.last s := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hil
      rw [hr j (by omega)]
      exact Matrix.one_apply_ne (fun e => hj (by rw [← e]; rfl))
end Formalism.L2.Col
