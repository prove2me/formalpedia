-- Prove2me | solution 1 for Formalism.L2.Geo.Def.G1.globLat_unimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:17:43.433821+00:00
-- url     : https://prove2.me/submissions/b1e246ba-517d-4a9d-9bca-793e3b4d2edb

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_GlobLatUnimod
import Theorems.Thm_Formalism_L2_Geo_Def_G1_star_int
import Theorems.Thm_Formalism_L2_Geo_Def_G1_mem_one_iff
import Theorems.Thm_Formalism_L2_Geo_Def_G1_hform_sig
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_L2_Geo_Def_G1_IsFrame_map
import Theorems.Thm_Formalism_L2_Geo_Def_G1_dual_frame
import Theorems.Thm_Formalism_L2_Geo_Def_G1_isFrame_of
import Theorems.Thm_Formalism_UG_P_csDual_sig_incl
import Theorems.Thm_Formalism_UG_P_csDual_span
import Theorems.Thm_Formalism_UG_P_csGlob_int
import Theorems.Thm_Formalism_UG_P_csScale_glob
import Theorems.Thm_Formalism_UG_P_hform_mulVec
import Theorems.Thm_Formalism_UG_P_integral_adele_approximation_holds
import Theorems.Thm_Formalism_UG_P_span_recovery_of_integral_adelic_approx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.Geo.Def.G1
theorem _root_.solution {n : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ x, σ x = star x) (J : Matrix (Fin n) (Fin n) E)
    (hs : (Formalism.DivisionValues.hform J).IsSymm) (hnd : (Formalism.DivisionValues.hform J).Nondegenerate)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.DivisionValues.hform J) Λ)
    (g : GL (Fin n) 𝒜) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.DivisionValues.hform J) (Formalism.UG.CS.globLat g Λ) := by
  have mem := Formalism.HermitianLatticesTheory.dualBasic_mem_dual (R := 𝓞 E) (Formalism.DivisionValues.hform J)
  have hstar : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := star_int
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.fg
  have hspan := hΛ.span_eq_top
  have hU' : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform J) Λ = Λ := hU
  show Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform J) (Formalism.UG.CS.globLat g Λ) = Formalism.UG.CS.globLat g Λ
  ext x
  rw [mem]
  constructor
  · intro hx
    obtain ⟨k, gg, w, hgg, hw, hfr⟩ := dual_frame (R := 𝓞 E) (Formalism.DivisionValues.hform J) hs hnd hstar Λ hΛ
    rw [hU'] at hw
    have hF := isFrame_of J gg w hfr
    have hx' : ∀ y ∈ Formalism.UG.CS.globLat g Λ, hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range := by
      intro y hy
      rw [hform_sig σ hσ]
      exact Submodule.mem_one.mp (hx y hy)
    have hUg : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) ((g : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) * J.map ιA *
        (g : Matrix (Fin n) (Fin n) 𝒜) = J.map ιA := hg
    obtain ⟨z, hz⟩ : ∃ z, z = ((g⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ (fun i => ιA (x i)) := ⟨_, rfl⟩
    have hxz : (fun i => ιA (x i)) = (g : Matrix (Fin n) (Fin n) 𝒜) *ᵥ z := by
      rw [hz, mulVec_mulVec, Units.mul_inv, one_mulVec]
    have hwz : ∀ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ,
        hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) u z ∈ 𝒮 := by
      intro u hu
      have hu' := (span_recovery_of_integral_adelic_approx integral_adele_approximation_holds F E (Fin n) Λ hfin hspan g
        ((g : Matrix (Fin n) (Fin n) 𝒜) *ᵥ u)).2 (by rwa [mulVec_mulVec, Units.inv_mul, one_mulVec])
      have := csDual_span σ J (Formalism.UG.CS.globLat g Λ) x hx' _ hu'
      rwa [hxz, hform_mulVec, hUg] at this
    have hzz := hF.map ιA (sigR σ (FiniteAdeleRing (𝓞 F) F))
      (fun a => by rw [csDual_sig_incl, hσ]) z
    show ((g⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ (fun i => ιA (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ
    rw [← hz, hzz]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : (fun c => ιA (w i c)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ :=
      Submodule.subset_span ⟨w i, hw i, rfl⟩
    have h2 : (fun c => ιA (gg i c)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ :=
      Submodule.subset_span ⟨gg i, hgg i, rfl⟩
    exact Submodule.smul_mem _ (⟨_, hwz _ h1⟩ : 𝒮) h2
  · intro hx y hy
    have hm : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (((1 : ℤ) : E) * hform (σ : E →+* E) J x y) := by
      intro a ha b hb
      rw [hform_sig σ hσ, Int.cast_one, one_mul, ← mem_one_iff]
      rw [← hU', mem] at hb
      exact hb a ha
    have h1 := csScale_glob σ J Λ 1 hm g hg hy hx
    have h2 := csGlob_int _ h1
    rw [hform_sig σ hσ, Int.cast_one, one_mul] at h2
    exact (mem_one_iff _).2 h2
end Formalism.L2.Geo.Def.G1
