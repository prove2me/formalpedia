-- Prove2me | solution 1 for Formalism.HN.DualPolygon.covol_map_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:12.557842+00:00
-- url     : https://prove2.me/submissions/5d86ffc2-0db4-4cd0-b5a2-e1fce9cd5e90

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_F_covolEqGram


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
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (φ : E →ₗ[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hφ : ∀ x y, inner ℝ (φ x) (φ y) = c ^ 2 * inner ℝ x y) (M : Submodule ℤ E)
    [DiscreteTopology M] :
    DiscreteTopology (M.map (φ.restrictScalars ℤ)) ∧
      Formalism.F.rk (M.map (φ.restrictScalars ℤ)) = Formalism.F.rk M ∧
      Formalism.F.covol (M.map (φ.restrictScalars ℤ)) = c ^ Formalism.F.rk M * Formalism.F.covol M := by
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hφ x x
    rw [hx, inner_zero_left] at h1
    have h2 : inner ℝ x x = (0 : ℝ) := by
      have hc2 : c ^ 2 ≠ 0 := pow_ne_zero _ hc.ne'
      exact (mul_eq_zero.1 h1.symm).resolve_left hc2
    exact inner_self_eq_zero.1 h2
  have hinjZ : Function.Injective (φ.restrictScalars ℤ) := hinj
  set M' := M.map (φ.restrictScalars ℤ) with hM'
  let e : M ≃ₗ[ℤ] M' := Submodule.equivMapOfInjective (φ.restrictScalars ℤ) hinjZ M
  let φe : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo φ hinj
  have hdisc : DiscreteTopology M' := by
    let g : M' → M := fun y => ⟨φe.symm (y : E), by
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.1 y.2
      have : φe.symm (y : E) = x := by
        rw [← hxy]
        show φe.symm (φe x) = x
        exact φe.symm_apply_apply x
      rw [this]; exact hx⟩
    refine DiscreteTopology.of_continuous_injective (f := g) ?_ ?_
    · have hc' : Continuous (φe.symm : E → E) :=
        LinearMap.continuous_of_finiteDimensional (φe.symm : E →ₗ[ℝ] E)
      exact Continuous.subtype_mk (hc'.comp continuous_subtype_val) _
    · intro y y' h
      have h' : φe.symm (y : E) = φe.symm (y' : E) := congrArg Subtype.val h
      exact Subtype.ext (φe.symm.injective h')
  have hrk : Formalism.F.rk M' = Formalism.F.rk M := by
    unfold Formalism.F.rk
    exact e.finrank_eq.symm
  refine ⟨hdisc, hrk, ?_⟩
  let b := Module.finBasis ℤ M
  let b' : Basis (Fin (finrank ℤ M)) ℤ M' := b.map e
  rw [Formalism.F.covolEqGram E M' _ b', Formalism.F.covolEqGram E M _ b]
  have hb' : ∀ i, (b' i : E) = φ (b i : E) := by
    intro i
    rw [Basis.map_apply]
    rfl
  have hG : Matrix.gram ℝ (fun i => (b' i : E)) = (c ^ 2) • Matrix.gram ℝ (fun i => (b i : E)) := by
    ext i j
    simp only [Matrix.gram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hb']
    rw [hφ]
  rw [hG, Matrix.det_smul, Fintype.card_fin]
  have hnn : 0 ≤ (c ^ 2) ^ finrank ℤ M := by positivity
  rw [Real.sqrt_mul hnn, ← pow_mul, mul_comm 2, pow_mul, Real.sqrt_sq (by positivity)]
  rfl
end Formalism.HN.DualPolygon
