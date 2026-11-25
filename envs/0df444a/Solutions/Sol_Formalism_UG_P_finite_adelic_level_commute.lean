-- Prove2me | solution 1 for Formalism.UG.P.finite_adelic_level_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:24:14.418811+00:00
-- url     : https://prove2.me/submissions/21d95711-a672-4c9f-8b58-c5884b27d8f5

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelafC_mul
import Theorems.Thm_Formalism_UG_P_levelaf_finite_quot
import Theorems.Thm_Formalism_UG_P_levelaf_princ_le_map_conj
import Theorems.Thm_Formalism_UG_P_levelaf_princ_relIndex_ne_zero
import Theorems.Thm_Formalism_UG_P_levelaf_exists_denom
import Theorems.Thm_Formalism_UG_P_stabilizer_standard_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.LevelAfComm := by
  intro F E _ _ _ _ _ n _ _ σ J g
  obtain ⟨d, hd0, c, hc, hg, hg'⟩ := levelaf_exists_denom (E := E) (n := n)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  have hcc : ((c * c : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) :
      E ⊗[F] FiniteAdeleRing (𝓞 F) F) = levelafC E (d * d) := by
    rw [levelafC_mul, ← hc]; rfl
  have hfin : Finite (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) ⧸
      Ideal.span {c * c}) := levelaf_finite_quot (d * d) (mul_ne_zero hd0 hd0) (c * c) hcc
  have hP := levelaf_princ_le_map_conj _ (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) c hg hg'
  have hne := levelaf_princ_relIndex_ne_zero (n := n)
    (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Ideal.span {c * c})
  have hstab : stabGL (stdLat (n := n) (A := E ⊗[F] FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))) =
      (bc (n := n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype).range :=
    stabilizer_standard_lattice _ _ n Subtype.val_injective
  have hLU : levelAf σ J ≤ UPts σ J (FiniteAdeleRing (𝓞 F) F) := inf_le_left
  have hLS : levelAf σ J ≤
      (bc (n := n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype).range :=
    hstab ▸ inf_le_right
  have h1 : (princ (n := n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype
      (Ideal.span {c * c})).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) ≤
      ((levelAf σ J).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))).map
        (MulAut.conj g).toMonoidHom := by
    intro h hh
    rw [Subgroup.mem_subgroupOf] at hh
    obtain ⟨l, hl, hlh⟩ := Subgroup.mem_map.1 (hP hh)
    refine Subgroup.mem_map.2 ⟨g⁻¹ * h * g, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.2 ⟨(g⁻¹ * h * g).2, ?_⟩
      have : ((g⁻¹ * h * g : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
          GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = l := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hlh, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        group
      rw [this, hstab]; exact hl
    · apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have h2 : ((princ (n := n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype
      (Ideal.span {c * c})).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))).relIndex
      ((levelAf σ J).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) ≠ 0 := by
    rw [Subgroup.relIndex_subgroupOf hLU]
    intro h0
    exact hne (Subgroup.relIndex_eq_zero_of_le_right hLS h0)
  intro h0
  have hd := Subgroup.relIndex_dvd_of_le_left
    ((levelAf σ J).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) h1
  rw [h0] at hd
  exact h2 (Nat.eq_zero_of_zero_dvd hd)
end Formalism.UG.P
