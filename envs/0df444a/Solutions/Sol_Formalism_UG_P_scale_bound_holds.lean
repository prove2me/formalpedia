-- Prove2me | solution 1 for Formalism.UG.P.scale_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:58:55.382906+00:00
-- url     : https://prove2.me/submissions/f3753c86-46be-4692-8813-0baf96d7de88

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Theorems.Thm_Formalism_UG_P_csScale_den
import Theorems.Thm_Formalism_UG_P_csScale_glob
import Theorems.Thm_Formalism_UG_P_adelstabL_den
import Theorems.Thm_Formalism_UG_P_adelstab_dual
import Theorems.Thm_Formalism_UG_P_adelstab_tr_mem


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
theorem _root_.solution : Formalism.UG.CS.ScaleBound := by
  intro F E _ _ _ _ _ n _ _ σ J Λ hfin _
  classical
  obtain ⟨m, hm0, hm⟩ := csScale_den σ J Λ hfin
  set β := Module.finBasis F E
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  obtain ⟨m1, hm10, hm1⟩ := adelstabL_den (fun i => β i)
  obtain ⟨m2, hm20, hm2⟩ := adelstabL_den (fun i => β' i)
  refine ⟨((m * m1 * m2 : ℤ) : 𝓞 E), ?_, fun g hg x hx y hy => ?_⟩
  · exact_mod_cast mul_ne_zero (mul_ne_zero hm0 hm10) hm20
  · set e := (m : E) * hform (σ : E →+* E) J x y with he_def
    have he : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e ∈
        tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) :=
      csScale_glob σ J Λ m hm g hg hx hy
    have h1 := adelstab_dual β (m1 : E) hm1 e (adelstab_tr_mem e he)
    have h2 : IsIntegral ℤ ((m2 : E) * ((m1 : E) * e)) := by
      suffices hs : ∀ z ∈ Submodule.span (𝓞 F) (Set.range β'), IsIntegral ℤ ((m2 : E) * z) from
        hs _ h1
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact hm2 i
      | zero => rw [mul_zero]; exact isIntegral_zero
      | add z z' _ _ h h' => rw [mul_add]; exact h.add h'
      | smul c z _ h =>
        rw [Algebra.smul_def, mul_left_comm]
        exact ((RingOfIntegers.isIntegral_coe c).algebraMap).mul h
    refine ⟨⟨_, h2⟩, ?_⟩
    show (m2 : E) * ((m1 : E) * e) = algebraMap (𝓞 E) E ((m * m1 * m2 : ℤ) : 𝓞 E) * _
    rw [he_def, map_intCast]
    push_cast
    ring
end Formalism.UG.P
