-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.norm_hcompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:13.421057+00:00
-- url     : https://prove2.me/submissions/455755a5-d097-4406-b9a1-a6fb4fdfe6d3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_coeOF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z5
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
variable (I : AutInst)
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
theorem _root_.solution (p : Ideal (𝓞 I.E)) [hp : p.IsPrime] (s : 𝓞 I.E)
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := I.E) p) :
    ∃ a : 𝓞 I.F, algebraMap (𝓞 I.F) (𝓞 I.E) a ∉ p ∧ ∃ t : 𝓞 I.E, algebraMap (𝓞 I.F) (𝓞 I.E) a = t * s := by
  have hinj : Function.Injective (algebraMap (𝓞 I.E) I.E) := IsFractionRing.injective (𝓞 I.E) I.E
  have hP : s ∉ p ∧ ∀ t : 𝓞 I.E, algebraMap (𝓞 I.E) I.E t = star (algebraMap (𝓞 I.E) I.E s) → t ∉ p := by
    unfold Formalism.HermitianLatticesTheory.hcompl at hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one =>
      refine ⟨fun h => hp.ne_top ((Ideal.eq_top_iff_one p).2 h), fun t ht h => hp.ne_top ((Ideal.eq_top_iff_one p).2 ?_)⟩
      have : t = 1 := hinj (by rw [ht, map_one, star_one])
      rwa [this] at h
    | mul x y _ _ hx hy =>
      refine ⟨fun h => (hp.mem_or_mem h).elim hx.1 hy.1, fun t ht h => ?_⟩
      obtain ⟨tx, htx⟩ := DictLat.star_int I x
      obtain ⟨ty, hty⟩ := DictLat.star_int I y
      have : t = tx * ty := hinj (by rw [ht, map_mul, map_mul, star_mul', htx, hty])
      rw [this] at h
      exact (hp.mem_or_mem h).elim (hx.2 tx htx) (hy.2 ty hty)
  obtain ⟨t, ht⟩ := DictLat.star_int I s
  have hfix : star (algebraMap (𝓞 I.E) I.E (t * s)) = algebraMap (𝓞 I.E) I.E (t * s) := by
    rw [map_mul, star_mul', ht, star_star, mul_comm]
  obtain ⟨f, hf⟩ := (I.cm.fixed _).1 hfix
  have hfint : IsIntegral ℤ f := by
    have h1 : IsIntegral ℤ (algebraMap I.F I.E f) := by rw [hf]; exact (t * s).isIntegral_coe
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ I.F I.E) (algebraMap I.F I.E).injective).1 h1
  have hαE : algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) ⟨f, hfint⟩) = algebraMap (𝓞 I.E) I.E (t * s) := by
    exact (coeOF I ⟨f, hfint⟩).trans hf
  have heq := hinj hαE
  refine ⟨⟨f, hfint⟩, ?_, t, heq⟩
  rw [heq]
  exact fun h => (hp.mem_or_mem h).elim (hP.2 t ht) hP.1
end Formalism.L2.SG.Pf.LatDictZ.Z5
