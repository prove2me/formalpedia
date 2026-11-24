-- Prove2me | solution 1 for Formalism.ExtensionFiltration.idealScale_mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:08.412693+00:00
-- url     : https://prove2.me/submissions/247fe4f4-075d-4352-b1e0-0e9f133d0ced

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Theorems.Thm_Formalism_ExtensionFiltration_covol_ideal_smul
import Theorems.Thm_Formalism_ExtensionFiltration_den_smul_idealSmul
import Theorems.Thm_P2M_Formalism_ExtensionFiltration_rkK_pos__577b2a56145a
import Theorems.Thm_Formalism_ExtensionFiltration_muDef_eq_covol
import Theorems.Thm_Formalism_F_covolPos
import Theorems.Thm_Formalism_HN_DualPolygon_twist_span_smul
import Theorems.Thm_Formalism_HN_place_lattice_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open scoped Pointwise
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.ExtensionFiltration
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) (hM0 : M ≠ ⊥) :
    (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M).FG ∧
      rkK (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) = rkK M ∧
      muDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  set N := Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M with hNdef
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  have hd0 : d ≠ 0 := nonZeroDivisors.coe_ne_zero I.den
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
    intro h0
    exact hd0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
  have hJ : I.num ≠ ⊥ := fun h => hI (FractionalIdeal.num_eq_zero_iff.1 h)
  have hD : Ideal.span {d} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hd0
  have heq : Ideal.span {d} • N = I.num • M := den_smul_idealSmul I M
  have heq' : d • N = I.num • M := by rw [← heq, Submodule.ideal_span_singleton_smul]
  let ψ : V →ₗ[𝓞 K] V :=
    (((algebraMap (𝓞 K) K d)⁻¹ • LinearMap.id : V →ₗ[K] V)).restrictScalars (𝓞 K)
  have hψ : ∀ z : V, ψ (d • z) = z := by
    intro z
    show (algebraMap (𝓞 K) K d)⁻¹ • (d • z) = z
    rw [← algebraMap_smul K d z, smul_smul, inv_mul_cancel₀ hdK, one_smul]
  have hNmap : N = (I.num • M).map ψ := by
    ext z
    constructor
    · intro hz
      refine ⟨d • z, ?_, hψ z⟩
      rw [← heq']
      exact Submodule.smul_mem_pointwise_smul _ _ _ hz
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, ← heq'] at hy
      obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      rw [hψ]
      exact hz
  have hNfg : N.FG := by
    rw [hNmap]
    exact (Submodule.FG.smul (IsNoetherian.noetherian I.num) hM).map _
  have hrk : rkK N = rkK M := by
    unfold rkK
    rw [← Formalism.HN.DualPolygon.twist_span_smul N _ hD, heq, Formalism.HN.DualPolygon.twist_span_smul M _ hJ]
  refine ⟨hNfg, hrk, ?_⟩
  have c1 := covol_ideal_smul b X hX N hNfg _ hD
  have c2 := covol_ideal_smul b X hX M hM _ hJ
  rw [heq, c2, hrk] at c1
  obtain ⟨hMlat, -, -⟩ := place_lattice_structure K V ι b X hX M hM
  obtain ⟨hNlat, -, -⟩ := place_lattice_structure K V ι b X hX N hNfg
  have hcM := Formalism.F.covolPos _ _ hMlat.2
  have hcN := Formalism.F.covolPos _ _ hNlat.2
  have hr : (0 : ℝ) < rkK M := by exact_mod_cast rkK_pos' M hM0
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hJpos : (0 : ℝ) < (Ideal.absNorm I.num : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hJ (Ideal.absNorm_eq_zero_iff.1 h))
  have hDpos : (0 : ℝ) < (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hD (Ideal.absNorm_eq_zero_iff.1 h))
  have hnorm : ((FractionalIdeal.absNorm I : ℚ) : ℝ) =
      (Ideal.absNorm I.num : ℝ) / (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    rw [FractionalIdeal.absNorm_eq, Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    push_cast
    rfl
  have hlog := congrArg Real.log c1
  rw [Real.log_mul (pow_pos hJpos _).ne' hcM.ne', Real.log_mul (pow_pos hDpos _).ne' hcN.ne',
    Real.log_pow, Real.log_pow] at hlog
  rw [muDef_eq_covol b X hX N hNfg, muDef_eq_covol b X hX M hM, hrk, hnorm,
    Real.log_div hJpos.ne' hDpos.ne']
  have hcNeq : Real.log (Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N)) =
      (rkK M : ℝ) * Real.log (Ideal.absNorm I.num : ℝ) +
        Real.log (Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) M)) -
        (rkK M : ℝ) * Real.log (Ideal.absNorm (Ideal.span {d}) : ℝ) := by linarith
  rw [hcNeq]
  field_simp
  ring
end Formalism.ExtensionFiltration
