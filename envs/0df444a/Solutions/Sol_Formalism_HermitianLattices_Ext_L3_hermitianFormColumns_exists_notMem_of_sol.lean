-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.exists_notMem_of_sol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:42.395638+00:00
-- url     : https://prove2.me/submissions/51a70047-1d0e-4f61-af0e-71f18d76bc17

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_fm_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_vecMul_adjugate
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_vecMul_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {H : Matrix m m (𝓞 K)}
    (hH : Hᴴ = H) {D n : 𝓞 F} (hD : H.det = ι D) {d v c k : ℕ} (hDd : D ∉ 𝔭 ^ (d + 1))
    (hn : n ∉ 𝔭 ^ (v + 1)) (hk : d + v + 1 ≤ k) (hc : d + v + 1 ≤ 2 * (c + 1)) {x : m → 𝓞 K}
    (hx : fm H x x - ι n ∈ extP K 𝔭 ^ k) : ∃ j, (star x ᵥ* H) j ∉ extP K 𝔭 ^ (c + 1) := by
  have hF : IsFixF K F := Fact.out
  by_contra hall
  push_neg at hall
  have h1 : ∀ i, ι D * star (x i) ∈ extP K 𝔭 ^ (c + 1) := by
    intro i
    have h2 := vecMul_mem hall H.adjugate i
    rw [vecMul_adjugate, hD, Pi.smul_apply, smul_eq_mul] at h2
    exact h2
  have h3 : ∀ i, ι D * x i ∈ extP K 𝔭 ^ (c + 1) := by
    intro i
    have h4 := conjO_mem_pow hF 𝔭 (c + 1) _ (h1 i)
    rw [map_mul, conjO_map hF, ← idealPowerSpanBounds.star_def, star_star] at h4
    exact h4
  have h5 : ι D * fm H x x ∈ extP K 𝔭 ^ (d + v + 1) := by
    rw [fm_eq]
    simp only [dotProduct, Finset.mul_sum]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    have h6 : (star x ᵥ* H) i * (ι D * x i) ∈ extP K 𝔭 ^ ((c + 1) + (c + 1)) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul (hall i) (h3 i)
    have e : ι D * ((star x ᵥ* H) i * x i) = (star x ᵥ* H) i * (ι D * x i) := by ring
    rw [e]
    exact Ideal.pow_le_pow_right (by omega) h6
  have h7 : ι D * (fm H x x - ι n) ∈ extP K 𝔭 ^ (d + v + 1) :=
    Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk hx)
  have h8 : ι (D * n) ∈ extP K 𝔭 ^ (d + v + 1) := by
    have e : ι (D * n) = ι D * fm H x x - ι D * (fm H x x - ι n) := by
      rw [map_mul]
      ring
    rw [e]
    exact Ideal.sub_mem _ h5 h7
  rw [mem_pow_iff] at h8
  exact idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hDd hn h8
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
