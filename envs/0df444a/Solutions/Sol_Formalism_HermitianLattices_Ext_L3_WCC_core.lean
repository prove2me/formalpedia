-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCC.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:30.371463+00:00
-- url     : https://prove2.me/submissions/0f464f3e-6d66-4059-8bf3-389aac75384f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LaurentAdjoinEqOfImageEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_WCC
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_conj
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsE_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_cayley
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_conj
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_div
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_div
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_form
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCB_exists_cayley
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCB_mem_of_resolvent
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCB_skewY_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCB_skewY_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCB_skewY_skew
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_inv_theta
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_exists_theta
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCC
open WCA WCB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.WCC
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (han : ∀ x, h x x = 0 → x = 0) {A : Submodule (𝓞 K) V} (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {v : ℕ} (hv : n ∉ 𝔭 ^ (v + 1))
    {x y : V} (hx : InL 𝔭 A 0 x) (hxx : h x x = κ (ι n)) (hyy : h y y = κ (ι n)) {J : ℕ}
    (hJ : 1 ≤ J) (hw : InL 𝔭 A (v + (v + J)) (y - x)) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ z, InL 𝔭 A 0 z → InL 𝔭 A J (g z - z)) ∧
      (∀ z, InL 𝔭 A 0 z → InL 𝔭 A 0 (g.symm z)) ∧ g x = y := by
  classical
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨θ₀, hθ₀⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := idealPowerSpanBounds.exists_inv_theta (K := K) hθ₀ 1
  have hconj : κ (conjO K θ₀) = star (κ θ₀) := rfl
  set δ : K := κ θ₀ - star (κ θ₀) with hδ
  have hδe : InI 𝔭 1 (δ * κ e - 1) := by
    refine ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), _, he, ?_⟩
    simp [hδ, hconj]
  obtain ⟨hne, hinv⟩ := InI.unit h𝔭 hF hδe
  have hδe' : 1 + (δ * κ e - 1) = δ * κ e := by ring
  rw [hδe'] at hne hinv
  have hδ0 : δ ≠ 0 := left_ne_zero_of_mul hne
  have he0 : κ e ≠ 0 := right_ne_zero_of_mul hne
  have hstarδ : star δ = -δ := by
    rw [hδ, star_sub, star_star]
    ring
  set l : K := κ θ₀ * δ⁻¹ with hl_def
  have hl : l + star l = 1 := by
    have h1 : l + star l = (κ θ₀ - star (κ θ₀)) * δ⁻¹ := by
      rw [hl_def, star_mul', star_inv₀, hstarδ, inv_neg]
      ring
    rw [h1]
    exact mul_inv_cancel₀ hδ0
  have hl0 : InI 𝔭 0 l := by
    have h1 := InI.mul hp (InI.int hp θ₀) (InI.mul hp (InI.int hp e) hinv)
    have h2 : κ e * (δ * κ e)⁻¹ = δ⁻¹ := by
      rw [mul_inv, mul_comm δ⁻¹, ← mul_assoc, mul_inv_cancel₀ he0, one_mul]
    rw [h2] at h1
    exact h1
  have hls0 : InI 𝔭 0 (star l) := InI.conj hF hl0
  set d : V := y - x with hd
  have hy : y = x + d := by simp [hd]
  have hexp : ∀ a b : V, h (a + b) (a + b) = h a a + h a b + h b a + h b b := by
    intro a b
    simp only [map_add, LinearMap.add_apply]
    ring
  have hdd : h x d + h d x + h d d = 0 := by
    have h1 := hexp x d
    rw [← hy, hyy, hxx] at h1
    linear_combination -h1
  set z₀ : V := x + star l • d with hz₀
  have hdL : InL 𝔭 A 0 (star l • d) := (InL.smul hp hls0 hw).mono (by omega)
  have hz₀L : InL 𝔭 A 0 z₀ := InL.add hp hx hdL
  have hsymm : ∀ a b : V, star (h a b) = h b a := fun a b => by
    simpa [starRingEnd_apply] using hs.eq a b
  set c : K := h z₀ z₀ with hc_def
  have hcstar : star c = c := hsymm z₀ z₀
  have hn0 : κ (ι n) ≠ 0 := κι_ne_zero hn
  have hcn : InI 𝔭 (v + (v + J)) (c - κ (ι n)) := by
    have h1 : c - κ (ι n) = h (star l • d) z₀ + h x (star l • d) := by
      rw [hc_def, hz₀]
      simp only [map_add, LinearMap.add_apply]
      rw [hxx]
      ring
    rw [h1]
    exact InI.add hp ((InL.form hp hF hA (InL.smul hp hls0 hw) hz₀L).mono (by omega))
      ((InL.form hp hF hA hx (InL.smul hp hls0 hw)).mono (by omega))
  set ε : K := (κ (ι n))⁻¹ * (c - κ (ι n)) with hε_def
  have hεv : InI 𝔭 (v + J) ε := InI.div h𝔭 hn hv hcn
  obtain ⟨hne', hinv'⟩ := InI.unit h𝔭 hF (hεv.mono (by omega))
  have hc : c = κ (ι n) * (1 + ε) := by
    rw [hε_def, mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
    ring
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero hn0 hne'
  have hcinv : c⁻¹ = (1 + ε)⁻¹ * (κ (ι n))⁻¹ := by
    rw [hc, mul_inv, mul_comm]
  set w : V := c⁻¹ • d with hw_def
  have hwv : InL 𝔭 A (v + J) w := by
    rw [hw_def, hcinv, mul_smul]
    exact (InL.smul hp hinv' (InL.div h𝔭 hn hv hw)).mono (by omega)
  have hwJ : InL 𝔭 A J w := hwv.mono (by omega)
  have hw1 : InL 𝔭 A 1 w := hwv.mono (by omega)
  set θ : K := c⁻¹ * c⁻¹ * h d z₀ with hθ_def
  have hθJ : InI 𝔭 J θ := by
    have h1 : InI 𝔭 (v + (v + J)) (h d z₀) := (InL.form hp hF hA hw hz₀L).mono (by omega)
    have h2 := InI.div h𝔭 hn hv (InI.div h𝔭 hn hv h1)
    have h3 := InI.mul hp hinv' (InI.mul hp hinv' h2)
    have h4 : θ = (1 + ε)⁻¹ * ((1 + ε)⁻¹ *
        ((κ (ι n))⁻¹ * ((κ (ι n))⁻¹ * h d z₀))) := by
      rw [hθ_def, hcinv]
      ring
    rw [h4]
    exact h3.mono (by omega)
  have hθ1 : InI 𝔭 1 θ := hθJ.mono (by omega)
  have hskew : h d z₀ + h z₀ d = 0 := by
    rw [hz₀]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul,
      starRingEnd_apply, star_star]
    linear_combination hdd + h d d * hl
  have hθstar : star θ = -θ := by
    rw [hθ_def, star_mul', star_mul', star_inv₀, hcstar, hsymm]
    linear_combination c⁻¹ * c⁻¹ * hskew
  set Y : V →ₗ[K] V := WCB.skewY h z₀ w θ with hY_def
  have hY := WCB.skewY_skew hs z₀ w hθstar
  have hYz : Y z₀ = d := by
    rw [hY_def, WCB.skewY_apply]
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
    have hcoef : θ * c - h w z₀ = 0 := by
      rw [hw_def, LinearMap.map_smulₛₗ₂, starRingEnd_apply, star_inv₀,
        hcstar, smul_eq_mul, hθ_def]
      linear_combination c⁻¹ * h d z₀ * hcc
    rw [hcoef, zero_smul, zero_add, hw_def, smul_smul, hcc, one_smul]
  obtain ⟨g, hg, hgz, hs1, hs2⟩ := WCB.exists_cayley han hY hl
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨z', hz'⟩ := hs1 z
    have hz'L := WCB.mem_of_resolvent h𝔭 hF hA hz₀L hw1 hθ1 hls0 hz hz'
    rw [← hz', hgz]
    have h1 : z' + l • Y z' - (z' - star l • Y z') = (l + star l) • Y z' := by
      rw [add_smul]
      abel
    rw [h1, hl, one_smul]
    exact WCB.skewY_mem hp hF hA hz₀L hwJ hθJ hz'L
  · intro z hz
    obtain ⟨z', hz'⟩ := hs2 z
    have hz'' : z' - (-l) • Y z' = z := by
      rw [neg_smul, sub_neg_eq_add]
      exact hz'
    have hz'L := WCB.mem_of_resolvent h𝔭 hF hA hz₀L hw1 hθ1 (InI.neg hl0) hz hz''
    have hgs : g.symm z = z' - star l • Y z' := by
      rw [LinearEquiv.symm_apply_eq, hgz, hz']
    rw [hgs]
    exact InL.sub hp hz'L ((InL.smul hp hls0 (WCB.skewY_mem hp hF hA hz₀L hwJ hθJ hz'L)).mono
      (by omega))
  · have hx' : z₀ - star l • Y z₀ = x := by
      rw [hYz, hz₀]
      abel
    rw [← hx', hgz, hYz, hz₀, hy, add_assoc, ← add_smul, add_comm (star l) l, hl, one_smul]
end Formalism.HermitianLattices.Ext.L3.WCC
