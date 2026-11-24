-- Prove2me | solution 1 for Formalism.UG.P.dual_lattice_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:50:06.745932+00:00
-- url     : https://prove2.me/submissions/8cc97649-df21-4b93-9523-fcafdebe86b8

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Theorems.Thm_Formalism_UG_P_csDual_hform_smul_left
import Theorems.Thm_Formalism_UG_P_csDual_sig_C
import Theorems.Thm_Formalism_UG_P_csDual_span
import Theorems.Thm_Formalism_UG_P_csDual_expand
import Theorems.Thm_Formalism_UG_P_csDual_int_coe
import Theorems.Thm_Formalism_UG_P_adelstabL_den
import Theorems.Thm_Formalism_UG_P_adelstabL_incl_int
import Theorems.Thm_Formalism_UG_P_adelstabL_lower
import Theorems.Thm_Formalism_UG_P_adelstab_algebraMap_ne_zero
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C
import Theorems.Thm_Formalism_UG_P_hform_mulVec
import Theorems.Thm_Formalism_UG_P_sf_single


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution (hSpanRecover : Formalism.UG.CS.SpanRecover) : Formalism.UG.CS.DualBound := by
  intro F E _ _ _ _ _ n _ _ σ J Λ hdet hfin hspan
  obtain ⟨c, hc, hlow⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : n × n => (J⁻¹) p.1 p.2)
  have haint : IsIntegral ℤ (algebraMap (𝓞 F) E (c * c) * (m : E)) := by
    refine (csDual_int_coe (c * c)).mul ?_
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E m))
  have ha0 : algebraMap (𝓞 F) E (c * c) * (m : E) ≠ 0 :=
    mul_ne_zero (adelstab_algebraMap_ne_zero (F := F) (E := E) _ (mul_ne_zero hc hc))
      (Int.cast_ne_zero.2 hm0)
  refine ⟨⟨_, haint⟩, ?_, ?_⟩
  · intro h
    apply ha0
    exact congrArg (fun t : 𝓞 E => (t : E)) h
  intro g hg x hx
  have hU : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) ((g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) *
      (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hg
  obtain ⟨z, hz⟩ : ∃ z, z = ((g⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) :=
    ⟨_, rfl⟩
  have hxz : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) =
      (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z := by
    rw [hz, mulVec_mulVec, Units.mul_inv, one_mulVec]
  have hw : ∀ w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ,
      hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) w z ∈
        tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
    intro w hw
    have hu := (hSpanRecover F E n Λ hfin hspan g ((g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w)).2
      (by rwa [mulVec_mulVec, Units.inv_mul, one_mulVec])
    have := csDual_span σ J (Formalism.UG.CS.globLat g Λ) x hx _ hu
    rwa [hxz, hform_mulVec, hU] at this
  have hi : ∀ i, levelafC E c *
      ((J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *ᵥ z) i ∈
        tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
    intro i
    have h1 := hw _ (hlow (Pi.single i (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (fun k => by
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _))
    have h2 : (fun k => levelafC E c * (Pi.single i (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) : n → _) k) =
        levelafC E c • (Pi.single i (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) : n → _) := by
      funext k; simp [Pi.smul_apply]
    rwa [h2, csDual_hform_smul_left, csDual_sig_C, sf_single] at h1
  have hinv : (J⁻¹).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hz2 : (J⁻¹).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) *ᵥ
      ((J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *ᵥ z) = z := by
    rw [mulVec_mulVec, hinv, one_mulVec]
  have hv : ∀ k, levelafC E c * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (m : E) * z k ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
    intro k
    have := csDual_expand (F := F) (J⁻¹) ((J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *ᵥ z)
      (levelafC E c) (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (m : E)) k
    rw [hz2] at this
    rw [this]
    refine sum_mem fun i _ => mul_mem ?_ (hi i)
    rw [← map_mul]
    exact adelstabL_incl_int (F := F) _ (hm (k, i))
  have hlat := hlow _ hv
  show ((g⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E ⟨_, haint⟩ • x) i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
  convert hlat using 1
  have hsm : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
      ((algebraMap (𝓞 E) E ⟨_, haint⟩ • x) i)) =
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) E (c * c) * (m : E)) •
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact map_mul _ _ _
  rw [hsm, mulVec_smul, ← hz]
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, adelstab_incl_C]
  ring
end Formalism.UG.P
