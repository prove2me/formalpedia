-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.cokernel_finite_card_eq_inv_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:56.521518+00:00
-- url     : https://prove2.me/submissions/459bb011-3531-483e-a85d-3c7f05bacb30

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_relIndex_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mem_LL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_map_le_of_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_LL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_good_fin
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (hd : LocalDatum K R ψ) (n : ℕ) (Z : Matrix (Fin n) (Fin n) K)
    (hZ : IsInt R Z) (hdet : IsUnit Z.det) :
    Finite (coker R Z) ∧ (Nat.card (coker R Z) : ℝ) = (modK R Z.det)⁻¹ := by
  have hL := lat_LL (ι := Fin n) hd.isOpen hd.isCompact
  have hgood := good_fin hd n Z hdet
  have hle := map_le_of_int (ι := Fin n) (R := R) (M := Z) hZ
  set A := (LL R (Fin n)).map (mv Z) with hA
  have hne : A.relIndex (LL R (Fin n)) ≠ 0 := relIndex_ne_zero (lat_map hdet hL).op hL.cp
  have hone : (LL R (Fin n)).relIndex A = 1 := AddSubgroup.relIndex_eq_one.mpr hle
  have hdl : dl R Z = 1 / (A.relIndex (LL R (Fin n)) : ℝ) := by
    unfold dl
    rw [← hA]
    unfold gi
    rw [hone, Nat.cast_one]
  have hrange : (coeLin R : (Fin n → R) →ₗ[R] (Fin n → K)).toAddMonoidHom.range = LL R (Fin n) := by
    ext v
    constructor
    · intro hv
      obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hv
      rw [mem_LL]
      intro i
      exact (y i).2
    · intro hv
      rw [mem_LL] at hv
      exact AddMonoidHom.mem_range.mpr ⟨fun i => ⟨v i, hv i⟩, rfl⟩
  have hlat : (latZ R Z).toAddSubgroup =
      A.comap (coeLin R : (Fin n → R) →ₗ[R] (Fin n → K)).toAddMonoidHom := by
    ext x
    rw [Submodule.mem_toAddSubgroup, Formalism.DoubleCosetMeasures.P.mem_latZ, AddSubgroup.mem_comap, hA]
    constructor
    · rintro ⟨y, hy⟩
      exact AddSubgroup.mem_map.mpr ⟨coeLin R y, mem_LL.mpr fun i => (y i).2, hy⟩
    · intro hx
      obtain ⟨v, hv, hvx⟩ := AddSubgroup.mem_map.mp hx
      rw [mem_LL] at hv
      exact ⟨fun i => ⟨v i, hv i⟩, hvx⟩
  have hcard : Nat.card (coker R Z) = A.relIndex (LL R (Fin n)) := by
    have h : Nat.card (coker R Z) = (latZ R Z).toAddSubgroup.index := rfl
    rw [h, hlat, AddSubgroup.index_comap, hrange]
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne), ?_⟩
  rw [hcard, ← hgood, hdl, one_div, inv_inv]
end Formalism.FourierDecayAlt.P.A5x5
