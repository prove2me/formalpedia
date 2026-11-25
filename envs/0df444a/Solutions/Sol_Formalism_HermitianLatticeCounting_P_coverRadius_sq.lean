-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.coverRadius_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:07:02.587332+00:00
-- url     : https://prove2.me/submissions/a0b20cfd-5541-4f42-b909-0c895b0d4f81

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HadamardInequality_P_tr_chain
import Theorems.Thm_Formalism_HadamardInequality_P_tr_dual
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h1
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (M : Submodule ℤ V) (hMd : DiscreteTopology M)
    (hspan : Submodule.span ℝ (M : Set V) = ⊤) (κ : ℝ) (hκ : 0 < κ)
    (hdual : ∀ y ∈ Formalism.HadamardInequality.zdual M, y ≠ 0 → κ ≤ ‖y‖) (x : V) :
    ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) ^ 2 / (2 * κ) := by
  have := hMd
  obtain ⟨b, t, hbM, hli, ht0, -, hWs, hcov⟩ :=
    Formalism.HadamardInequality.P.tr_chain M hspan (Module.finrank ℝ V) le_rfl
  have hbspan : Submodule.span ℝ (Set.range b) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  obtain ⟨z, hz, hzx⟩ := hcov x (by rw [hbspan]; trivial)
  have hzM : z ∈ M :=
    (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbM i)) hz
  refine ⟨z, hzM, ?_⟩
  have ht : ∀ i, t i ≤ (Module.finrank ℝ V : ℝ) ^ ((3:ℝ)/2) / κ := by
    intro i
    obtain ⟨W, hWr, hWm⟩ := hWs i
    obtain ⟨y, hyD, hyli, hyn⟩ := Formalism.HadamardInequality.P.tr_dual M hspan W (ht0 i) hWm
    have hfr : Module.finrank ℝ W + Module.finrank ℝ Wᗮ = Module.finrank ℝ V :=
      Submodule.finrank_add_finrank_orthogonal W
    have hpos : 0 < Module.finrank ℝ Wᗮ := by have := i.2; omega
    have hy0 : y ⟨0, hpos⟩ ≠ 0 := hyli.ne_zero _
    have h1 := hdual _ (hyD ⟨0, hpos⟩) hy0
    have h2 := hyn ⟨0, hpos⟩
    have h3 : (Module.finrank ℝ Wᗮ : ℝ) ^ ((3:ℝ)/2) ≤ (Module.finrank ℝ V : ℝ) ^ ((3:ℝ)/2) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast (by omega : Module.finrank ℝ Wᗮ ≤ Module.finrank ℝ V)) (by norm_num)
    have h4 : κ ≤ (Module.finrank ℝ V : ℝ) ^ ((3:ℝ)/2) / t i :=
      h1.trans (h2.trans (div_le_div_of_nonneg_right h3 (ht0 i).le))
    rw [le_div_iff₀ (ht0 i)] at h4
    rw [le_div_iff₀ hκ]; linarith
  generalize Module.finrank ℝ V = N at *
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have h32 : ((N:ℝ) ^ ((3:ℝ)/2)) ^ 2 = (N:ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hsum : ∑ l, t l ^ 2 ≤ (N:ℝ) * ((N:ℝ) ^ 3 / κ ^ 2) := by
    calc ∑ l, t l ^ 2 ≤ ∑ _l : Fin N, ((N:ℝ) ^ ((3:ℝ)/2) / κ) ^ 2 :=
          Finset.sum_le_sum fun l _ => pow_le_pow_left₀ (ht0 l).le (ht l) 2
      _ = _ := by simp [div_pow, h32]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have e : ((N:ℝ) ^ 2 / (2 * κ)) ^ 2 = (N:ℝ) ^ 4 / κ ^ 2 / 4 := by
    field_simp; ring
  have e2 : (N:ℝ) * ((N:ℝ) ^ 3 / κ ^ 2) = (N:ℝ) ^ 4 / κ ^ 2 := by ring
  rw [e]
  linarith
end Formalism.HermitianLatticeCounting.P
