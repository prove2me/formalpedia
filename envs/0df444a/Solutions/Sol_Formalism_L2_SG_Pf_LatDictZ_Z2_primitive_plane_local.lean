-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z2.primitive_plane_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:57.839896+00:00
-- url     : https://prove2.me/submissions/4cf0ca19-1db6-4f4f-9621-83972cf7cc5d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_IdealLike_add
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_ring_core
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_partner
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_prim
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_planeForm_apply
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_idealLike
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_unit
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__400b9b0d74e1
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_star__10f2f234469a
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_trace_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_isHermSemilocal_locRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_hcompl_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
namespace Formalism.L2.SG.Pf.LatDictZ.Z2
theorem _root_.solution : Z0.PrimPlaneLoc := by
  intro K _ _ _ V _ _ _ h hK hs _ p hp N z b hN hz hprim hnu hb hbb hw
  obtain ⟨w, hzw, hww⟩ := hw
  have hS := isHermSemilocal_locRing hK hp
  have hpP := hp.isPrime
  have hsym : ∀ x y, star (h x y) = h y x := fun x y => hs.eq x y
  have hPl : IdealLike (locRing p) (InI p p) :=
    plane_idealLike hpP p (fun s hs' => ((mem_hcompl_iff hpP s).1 hs').1)
  have hQl : IdealLike (locRing p) (InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p)) :=
    plane_idealLike hpP _ (fun s hs' => ((mem_hcompl_iff hpP s).1 hs').2)
  have hunit : ∀ a ∈ locRing p, ¬ InI p p a → ¬ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a →
      IsUnitIn (locRing p) a := fun a ha h1 h2 => plane_unit hpP ha h1 h2

  have hζS : h z z ∈ locRing p := hN.int z hz z hz
  have hζr : star (h z z) = h z z := hsym z z
  have hJ : InI p p (h z z) ∧ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) (h z z) := by
    by_cases h1 : InI p p (h z z)
    · refine ⟨h1, ?_⟩
      have := plane_star₁ h1
      rwa [hζr] at this
    · have h2 : InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) (h z z) := by
        by_contra h2
        exact hnu (hunit _ hζS h1 h2)
      refine ⟨?_, h2⟩
      have := plane_star₂ h2
      rwa [hζr] at this
  have hu : IsUnitIn (locRing p) (1 - b * h z z) := by
    have hm : 1 - b * h z z ∈ locRing p := (locRing p).sub_mem (locRing p).one_mem ((locRing p).mul_mem hb hζS)
    refine hunit _ hm (fun h1 => hPl.2.2 ?_) (fun h1 => hQl.2.2 ?_)
    · convert hPl.add h1 (hPl.2.1 b hb _ hJ.1) using 1
      ring
    · convert hQl.add h1 (hQl.2.1 b hb _ hJ.2) using 1
      ring

  obtain ⟨q, hq⟩ : ∃ q : V →ₗ⋆[K] V →ₗ[K] K, ∀ x y, q x y = h x y - b * h x z * h z y :=
    ⟨planeForm h z b, planeForm_apply h z b⟩
  have hqsym : ∀ x y, star (q x y) = q y x := by
    intro x y
    rw [hq, hq, star_sub, star_mul', star_mul', hbb, hsym, hsym, hsym]
    ring
  have hqint : ∀ x ∈ N, ∀ y ∈ N, q x y ∈ locRing p := by
    intro x hx y hy
    rw [hq]
    exact (locRing p).sub_mem (hN.int x hx y hy)
      ((locRing p).mul_mem ((locRing p).mul_mem hb (hN.int x hx z hz)) (hN.int z hz y hy))
  have hqz : ∀ x, q z x = (1 - b * h z z) * h z x := by
    intro x
    rw [hq]
    ring
  have hqdual : ∀ x, (∀ m ∈ N, q m x ∈ locRing p) → x ∈ N := by
    intro x hx
    have hzx : h z x ∈ locRing p := by
      have := (locRing p).mul_mem hu.2.2 (hx z hz)
      rwa [hqz, ← mul_assoc, inv_mul_cancel₀ hu.1, one_mul] at this
    have hx' : x - (b * h z x) • z ∈ N := by
      apply hN.dual
      intro m hm
      convert hx m hm using 1
      rw [hq, map_sub, map_smul, smul_eq_mul]
      ring
    have := N.add_mem hx' (hN.smul_mem _ ((locRing p).mul_mem hb hzx) z hz)
    rwa [sub_add_cancel] at this

  have hwz : h w z = 1 := by rw [← hsym, hzw, star_one]
  have hqw : q w w = 0 := by rw [hq, hwz, hzw, hww]; ring
  obtain ⟨α, hα0, heN, heprim⟩ := plane_prim hS h hN.smul_mem hN.int hz hzw (hN.span w)
  have hze : h z (α • w) = α := by rw [map_smul, smul_eq_mul, hzw, mul_one]
  have hqee : q (α • w) (α • w) = 0 := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hqw, mul_zero]
  have hqez : q (α • w) z ≠ 0 := by
    rw [← hqsym, hqz, hze, star_mul']
    exact mul_ne_zero (star_ne_zero.mpr hu.1) (star_ne_zero.mpr hα0)
  generalize α • w = e at heN heprim hze hqee hqez

  obtain ⟨f₀, hf₀N, hef₀⟩ := plane_partner hS q hqsym hN.smul_mem hqint hqdual heN heprim hz hqez
  have hf₀e : q f₀ e = 1 := by rw [← hqsym, hef₀, star_one]
  obtain ⟨c₁, hc₁S, hc₁⟩ := exists_trace_eq hS (s := -q f₀ f₀)
    ((locRing p).neg_mem (hqint f₀ hf₀N f₀ hf₀N)) (by rw [star_neg, hqsym])
  have hfN : f₀ + c₁ • e ∈ N := N.add_mem hf₀N (hN.smul_mem c₁ hc₁S e heN)
  have hqef : q e (f₀ + c₁ • e) = 1 := by
    rw [map_add, map_smul, smul_eq_mul, hqee, mul_zero, add_zero, hef₀]
  have hqff : q (f₀ + c₁ • e) (f₀ + c₁ • e) = 0 := by
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, hqee, hef₀, hf₀e]
    linear_combination hc₁
  generalize f₀ + c₁ • e = f at hfN hqef hqff
  have hqfe : q f e = 1 := by rw [← hqsym, hqef, star_one]

  obtain ⟨t, htN, hzt⟩ := plane_partner hS h hsym hN.smul_mem hN.int hN.dual hz hprim heN
    (by rw [hze]; exact hα0)

  have hgN : t - q f t • e - q e t • f ∈ N :=
    N.sub_mem (N.sub_mem htN (hN.smul_mem _ (hqint f hfN t htN) e heN))
      (hN.smul_mem _ (hqint e heN t htN) f hfN)
  have hqeg : q e (t - q f t • e - q e t • f) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hqee, hqef]
    ring
  have hqfg : q f (t - q f t • e - q e t • f) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hqff, hqfe]
    ring
  have hzg : q f t * h z e + q e t * h z f + h z (t - q f t • e - q e t • f) = 1 := by
    simp only [map_sub, map_smul, smul_eq_mul, hzt]
    ring
  have hαS := hqint f hfN t htN
  have hβS := hqint e heN t htN
  generalize q f t = α' at hgN hqeg hqfg hzg hαS
  generalize q e t = β' at hgN hqeg hqfg hzg hβS
  generalize t - α' • e - β' • f = g at hgN hqeg hqfg hzg
  have hqge : q g e = 0 := by rw [← hqsym, hqeg, star_zero]
  have hqgf : q g f = 0 := by rw [← hqsym, hqfg, star_zero]
  obtain ⟨c, hcS, hc⟩ := exists_trace_eq hS (s := -q g g)
    ((locRing p).neg_mem (hqint g hgN g hgN)) (by rw [star_neg, hqsym])
  obtain ⟨θ, -, hμ⟩ := hS.unram
  have hμs : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star]; ring
  generalize θ - star θ = μ at hμ hμs

  have key : ∀ s a d : K, s ∈ locRing p → a ∈ locRing p → d ∈ locRing p →
      star s * s * q g g + star a * d + star d * a = 0 →
      IsUnitIn (locRing p) (s * h z g + a * h z e + d * h z f) → ∃ y ∈ N, h z y = 1 ∧ h y y = b := by
    intro s a d hs' ha hd hn hU
    have hXN : s • g + a • e + d • f ∈ N :=
      N.add_mem (N.add_mem (hN.smul_mem s hs' g hgN) (hN.smul_mem a ha e heN)) (hN.smul_mem d hd f hfN)
    have hzX : h z (s • g + a • e + d • f) = s * h z g + a * h z e + d * h z f := by
      simp only [map_add, map_smul, smul_eq_mul]
    have hqX : q (s • g + a • e + d • f) (s • g + a • e + d • f) = 0 := by
      rw [← hn]
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, RingHom.id_apply, hqee, hqff, hqef, hqfe, hqeg, hqge, hqfg, hqgf]
      ring
    refine ⟨(s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f),
      hN.smul_mem _ hU.2.2 _ hXN, ?_, ?_⟩
    · rw [map_smul, smul_eq_mul, hzX, inv_mul_cancel₀ hU.1]
    · have h1 : h z ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) = 1 := by
        rw [map_smul, smul_eq_mul, hzX, inv_mul_cancel₀ hU.1]
      have h2 : h ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) z = 1 := by
        rw [← hsym, h1, star_one]
      have h3 := hq ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f))
        ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f))
      rw [h1, h2] at h3
      have h4 : q ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f))
          ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) = 0 := by
        simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hqX, mul_zero]
      rw [h4] at h3
      linear_combination -h3
  have hS0 : (0 : K) ∈ locRing p := (locRing p).zero_mem
  have hS1 : (1 : K) ∈ locRing p := (locRing p).one_mem
  have hμS : μ ∈ locRing p := hμ.2.1
  have hcμ : c + μ ∈ locRing p := (locRing p).add_mem hcS hμS
  rcases plane_ring_core hPl hQl hunit (hN.int z hz e heN) (hN.int z hz f hfN) hαS hβS hcS hμ hzg with
    h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact key 0 1 0 hS0 hS1 hS0 (by simp) (by convert h1 using 1; ring)
  · exact key 0 0 1 hS0 hS0 hS1 (by simp) (by convert h1 using 1; ring)
  · exact key 0 1 μ hS0 hS1 hμS (by rw [hμs]; simp) (by convert h1 using 1; ring)
  · exact key 1 1 c hS1 hS1 hcS (by rw [star_one]; linear_combination hc) (by convert h1 using 1; ring)
  · exact key 1 1 (c + μ) hS1 hS1 hcμ (by rw [star_one, star_add, hμs]; linear_combination hc)
      (by convert h1 using 1; ring)
  · exact key 1 c 1 hS1 hcS hS1 (by rw [star_one]; linear_combination hc) (by convert h1 using 1; ring)
  · exact key 1 (c + μ) 1 hS1 hcμ hS1 (by rw [star_one, star_add, hμs]; linear_combination hc)
      (by convert h1 using 1; ring)
end Formalism.L2.SG.Pf.LatDictZ.Z2
