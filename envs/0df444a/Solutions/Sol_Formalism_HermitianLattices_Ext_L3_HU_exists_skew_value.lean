-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_skew_value
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:53.456217+00:00
-- url     : https://prove2.me/submissions/f1abcf9c-8739-49b6-aba9-cab526a898f9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_theta_inv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Hq_conjTranspose
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_star_inv_eq_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_fillO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mk_mem_ker_piQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_def
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open HermitianSublattices idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H E₀ : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) {d : 𝓞 F} {e : ℕ} (hd : d ∉ 𝔭 ^ (e + 1))
    (hHE : H * E₀ = algebraMap (𝓞 F) (𝓞 K) d • (1 : Matrix κ κ (𝓞 K))) {j : ℕ} (hj : e ≤ j)
    (S : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1))) (hS : S ∈ hermSub κ (RingHom.ker (piQ K 𝔭 j))) :
    ∃ Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)),
      Hq H 𝔭 (j + 1) * Y + Yᴴ * Hq H 𝔭 (j + 1) = S := by
  obtain ⟨θ, u, hu⟩ := exists_theta_inv hK h𝔭 (j + 1)
  have hτ : θ * u + star (θ * u) = 1 := by
    rw [star_mul', star_inv_eq_neg hu]
    linear_combination hu
  set mk := Ideal.Quotient.mk (extP K 𝔭 ^ (j + 1)) with hmk
  set dq := mk (algebraMap (𝓞 F) (𝓞 K) d) with hdq
  have hds : star dq = dq := by
    rw [hdq, hmk, star_mk, star_def, conjO_map Fact.out]
  have hfill : ∀ a b, ∃ r : 𝓞 K, S a b = dq * mk r := by
    intro a b
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (S a b)
    have hs' : s ∈ extP K 𝔭 ^ j := by
      rw [← mk_mem_ker_piQ, hs]
      exact hS.2 a b
    obtain ⟨r, -, hr⟩ := exists_fillO h𝔭 hd hj hs'
    refine ⟨r, ?_⟩
    rw [← hs, hdq, ← map_mul]
    exact Ideal.Quotient.eq.2 hr
  choose r hr using hfill
  set R : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)) := Matrix.of fun a b => mk (r a b) with hR
  have hSR : S = dq • R := by
    ext a b
    rw [hr a b]
    rfl
  have hSR' : S = dq • Rᴴ := by
    conv_lhs => rw [← hS.1, hSR, conjTranspose_smul, hds]
  have hHEq : Hq H 𝔭 (j + 1) * E₀.map mk = dq • (1 : Matrix κ κ _) := by
    rw [← Matrix.map_mul, hHE]
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
    rw [apply_ite mk, map_one, map_zero]
  have hEH : (E₀.map mk)ᴴ * Hq H 𝔭 (j + 1) = dq • (1 : Matrix κ κ _) := by
    have := congrArg conjTranspose hHEq
    rwa [conjTranspose_mul, Hq_conjTranspose hH, conjTranspose_smul, conjTranspose_one, hds] at this
  refine ⟨E₀.map mk * ((θ * u) • R), ?_⟩
  rw [← Matrix.mul_assoc, hHEq, conjTranspose_mul, Matrix.mul_assoc, hEH, conjTranspose_smul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_comm dq, ← hSR,
    smul_comm dq, ← hSR', ← add_smul, hτ, one_smul]
end Formalism.HermitianLattices.Ext.L3.HU
