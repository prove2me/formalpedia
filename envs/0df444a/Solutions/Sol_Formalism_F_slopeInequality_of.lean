-- Prove2me | solution 1 for Formalism.F.slopeInequality_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:02:53.027871+00:00
-- url     : https://prove2.me/submissions/3d54473f-c750-4b87-b87e-911351fc6559

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
import Theorems.Thm_Formalism_F_covol_pos_of_discrete
import Theorems.Thm_Formalism_F_norm_sum_smul_le_of_int
import Theorems.Thm_Formalism_F_covol_eq_gram
import Theorems.Thm_Formalism_F_gram_det_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
universe u v
namespace Formalism.F
theorem _root_.solution (h : SlopeLeMuMax.{v}) : SlopeInequality.{u, v} := by
  intro E F _ _ _ _ _ _ L M hL hM hne φ C hφ hC
  classical
  let g : L →ₗ[ℤ] F := M.subtype.comp φ
  have ginj : Function.Injective g := M.injective_subtype.comp hφ
  let N : Submodule ℤ F := LinearMap.range g
  have hNM : N ≤ M := by
    rintro _ ⟨x, rfl⟩
    exact (φ x).2
  haveI : DiscreteTopology L := hL
  haveI : DiscreteTopology M := hM
  haveI : DiscreteTopology N :=
    DiscreteTopology.of_continuous_injective (continuous_inclusion hNM)
      (Submodule.inclusion_injective hNM)
  let e : L ≃ₗ[ℤ] N := LinearEquiv.ofInjective g ginj

  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hφx : ((φ ⟨x, hxL⟩ : M) : F) ≠ 0 := by
    intro h0
    apply hx0
    have h1 : φ ⟨x, hxL⟩ = φ 0 := by
      rw [map_zero]
      exact Subtype.ext h0
    exact congrArg Subtype.val (hφ h1)
  have hNne : N ≠ ⊥ := by
    intro h0
    apply hφx
    have hmem : g ⟨x, hxL⟩ ∈ N := LinearMap.mem_range_self g _
    rw [h0, Submodule.mem_bot] at hmem
    exact hmem
  have hCpos : 0 < C := by
    have h1 : ‖((φ ⟨x, hxL⟩ : M) : F)‖ ≤ C * ‖x‖ := hC ⟨x, hxL⟩
    have h2 : 0 < ‖((φ ⟨x, hxL⟩ : M) : F)‖ := norm_pos_iff.mpr hφx
    have h3 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h3.le]
  have h1 : slope N ≤ muMax M := h F M N hM hNM hNne

  set r := Module.finrank ℤ L with hr_def
  have hrkL : rk L = r := rfl
  have hrkN : rk N = r := by
    show Module.finrank ℤ N = Module.finrank ℤ L
    exact e.finrank_eq.symm
  haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hrpos : 0 < r := Module.finrank_pos

  let b := Module.finBasis ℤ L
  have hcL : covol L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det :=
    covol_eq_gram E L (Fin r) b
  have hcN : covol N = Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det :=
    covol_eq_gram F N (Fin r) (b.map e)
  have hint : ∀ n : Fin r → ℤ,
      ‖∑ i, (n i : ℝ) • ((φ (b i) : M) : F)‖ ≤ C * ‖∑ i, (n i : ℝ) • (b i : E)‖ := by
    intro n
    have h2 := hC (∑ i, n i • b i)
    simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul] at h2
    simpa only [Int.cast_smul_eq_zsmul] using h2
  have hreal := norm_sum_smul_le_of_int (fun i => (b i : E))
    (fun i => ((φ (b i) : M) : F)) C hint
  have hdet := gram_det_le E F (Fin r) (fun i => (b i : E))
    (fun i => ((φ (b i) : M) : F)) C hreal
  have hle : covol N ≤ C ^ r * covol L := by
    rw [hcN, hcL]
    calc Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det
        ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin r)) *
            (Matrix.gram ℝ (fun i => (b i : E))).det) := Real.sqrt_le_sqrt hdet
      _ = C ^ r * Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det := by
        rw [Fintype.card_fin, show C ^ (2 * r) = (C ^ r) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hcLpos := covol_pos_of_discrete L
  have hcNpos := covol_pos_of_discrete N
  have hlog : Real.log (covol N) ≤ r * Real.log C + Real.log (covol L) := by
    have h2 := Real.log_le_log hcNpos hle
    rwa [Real.log_mul (by positivity) hcLpos.ne', Real.log_pow] at h2
  have hr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
  have hs : slope L ≤ slope N + Real.log C := by
    unfold slope deg
    rw [hrkL, hrkN, div_add' _ _ _ hr.ne', div_le_div_iff_of_pos_right hr]
    nlinarith
  linarith
end Formalism.F
