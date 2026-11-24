-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.step_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:25.572547+00:00
-- url     : https://prove2.me/submissions/2f64bbb2-7bb0-4d84-872d-adb195125be6

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_step_Z
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
open scoped Classical
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) {j : ℕ} (X : Fin j → Fin n → L)
    (hX : LinearIndependent L X) (g : Fin j → L) (a : L) (ha : a ^ Fintype.card K = a) (c : ℕ)
    (hc : c * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ n) :
    (Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ)
      ≤ c + (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n ∧
    (c : ℝ) - (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n
        - (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) ^ 2) ^ j
      ≤ (Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) := by
  have hZ := abs_le.1 (step_Z Ph h2 hPh hherm X hX g a ha c hc)
  set Z := univ.filter (fun x : Fin n → L => (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a) with hZd
  have hsplit := Finset.card_filter_add_card_filter_not (s := Z)
    (fun x => x ∈ Submodule.span L (Set.range X))
  have hs : Z.filter (fun x => ¬ x ∈ Submodule.span L (Set.range X))
      = univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a) := by
    ext x
    simp only [hZd, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hs] at hsplit
  have hspan : (Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card
      ≤ (Fintype.card K ^ 2) ^ j := by
    calc _ ≤ (univ.image fun cf : Fin j → L => ∑ b, cf b • X b).card := by
          refine Finset.card_le_card fun x hx => ?_
          obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 (Finset.mem_filter.1 hx).2
          exact Finset.mem_image.2 ⟨cf, Finset.mem_univ _, hcf⟩
      _ ≤ (univ : Finset (Fin j → L)).card := Finset.card_image_le
      _ = _ := by simp [card_L h2]
  have hspanR : ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ)
      ≤ ((Fintype.card K : ℝ) ^ 2) ^ j := by exact_mod_cast hspan
  have hsplitR : ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ)
      + ((univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) = (Z.card : ℝ) := by
    exact_mod_cast hsplit
  have hq0 : (0 : ℝ) ≤ (Fintype.card K : ℝ) := Nat.cast_nonneg _
  have h0 : (0 : ℝ) ≤ ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ) :=
    Nat.cast_nonneg _
  constructor
  · nlinarith [hZ.2]
  · nlinarith [hZ.1]
end Formalism.HermitianLatticeCounting.P.S4aux
