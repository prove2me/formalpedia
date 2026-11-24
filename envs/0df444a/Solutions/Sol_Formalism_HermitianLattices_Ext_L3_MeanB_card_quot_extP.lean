-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.card_quot_extP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:24.653383+00:00
-- url     : https://prove2.me/submissions/573d584f-06bc-466b-97b3-a67f472eed3d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_finrank_eq_two
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanA_card_quot_pow_smul_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.MeanB
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V * k) := by
  let _ : Module F V := Module.compHom V (algebraMap F K)
  have t1 : IsScalarTower F K V := ⟨fun a b v => by
    change (a • b) • v = (algebraMap F K a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let _ : Module (𝓞 F) V := Module.compHom V (algebraMap (𝓞 F) (𝓞 K))
  have t2 : IsScalarTower (𝓞 F) (𝓞 K) V := ⟨fun a b v => by
    change (a • b) • v = (algebraMap (𝓞 F) (𝓞 K) a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have t3 : IsScalarTower (𝓞 F) F V := ⟨fun a b v => by
    change (algebraMap F K (a • b)) • v = (algebraMap (𝓞 F) (𝓞 K) a) • ((algebraMap F K b) • v)
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) a), algebraMap_comp, Algebra.smul_def, map_mul,
      mul_smul]⟩
  have : FiniteDimensional F V := FiniteDimensional.trans F K V
  have hrank : finrank F V = 2 * finrank K V := by
    rw [← finrank_mul_finrank F K V, finrank_eq_two hK hF]
  let M : Submodule (𝓞 F) V := L.restrictScalars (𝓞 F)
  let e : ↥M ≃ₗ[𝓞 F] ↥L := (Submodule.restrictScalarsEquiv (𝓞 F) (𝓞 K) V L).restrictScalars (𝓞 F)
  have hfg : M.FG := by
    have : Module.Finite (𝓞 K) ↥L := Module.Finite.iff_fg.2 hL.fg
    have : Module.Finite (𝓞 F) ↥L := Module.Finite.trans (𝓞 K) ↥L
    exact Module.Finite.iff_fg.1 (Module.Finite.equiv e.symm)
  have hspan : Submodule.span F (M : Set V) = ⊤ := by
    have key : ∀ (a : K), ∀ w ∈ Submodule.span F (M : Set V), a • w ∈ Submodule.span F (M : Set V) := by
      intro a w hw
      induction hw using Submodule.span_induction with
      | mem l hl =>
        obtain ⟨d, hd, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2
          (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a)).exists_integral_multiple
        let z : 𝓞 K := ⟨d • a, hint⟩
        have hz : algebraMap (𝓞 K) K z = d • a := rfl
        have hd' : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
        have : a • l = ((d : F)⁻¹) • (z • l) := by
          rw [← algebraMap_smul K z l, hz, ← algebraMap_smul K ((d : F)⁻¹), smul_smul, map_inv₀,
            map_intCast, zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Int.cast_ne_zero.2 hd), one_mul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (L.smul_mem z hl))
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul f x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro v hv0
    clear hv0
    have hv : v ∈ Submodule.span K (L : Set V) := hL.span_eq_top ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem l hl => exact Submodule.subset_span hl
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact key a x hx
  have main := MeanA.card_quot_pow_smul_top (F := F) M hfg hspan h𝔭 k
  have hQ : Nat.card (𝓞 F ⧸ 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ k := by
    rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hmap : (𝔭 ^ k • ⊤ : Submodule (𝓞 F) ↥M).map (e : ↥M →ₗ[𝓞 F] ↥L) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L).restrictScalars (𝓞 F) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, extP, ← Ideal.map_pow,
      Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  have e1 := Submodule.Quotient.equiv _ _ e hmap
  have e2 := Submodule.Quotient.restrictScalarsEquiv (𝓞 F)
    ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)
  rw [← Nat.card_congr e2.toEquiv, ← Nat.card_congr e1.toEquiv, main, hQ, hrank, ← pow_mul]
  congr 1; ring
end Formalism.HermitianLattices.Ext.L3.MeanB
