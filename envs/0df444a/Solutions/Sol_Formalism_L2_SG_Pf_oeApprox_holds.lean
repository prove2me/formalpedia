-- Prove2me | solution 1 for Formalism.L2.SG.Pf.oeApprox_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:27.867869+00:00
-- url     : https://prove2.me/submissions/7d311d96-a9c2-498f-a00f-7bdb8e2a165e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipLat
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipLatPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf
namespace Formalism.L2.SG.Pf
theorem _root_.solution : Formalism.L2.SG.Pf.UnipLat.OEApprox := by
  intro F E _ _ _ _ _ _ hE _ φ hφ
  classical

  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
    (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis E))
  refine ⟨R, fun t => ?_⟩

  let w : InfinitePlace F → InfinitePlace E := fun v => InfinitePlace.mk (φ v)
  have hw : ∀ v, (w v).comap (algebraMap F E) = v := by
    intro v
    have hcomp : (φ v).comp (algebraMap F E) = v.embedding := RingHom.ext (hφ v)
    simp only [w, InfinitePlace.comap_mk, hcomp, InfinitePlace.mk_embedding]
  have hinj : ∀ v v', w v = w v' → v = v' := by
    intro v v' h
    rw [← hw v, ← hw v', h]
  let c : InfinitePlace F → ℂ := fun v =>
    if (w v).embedding = φ v then t v else (starRingEnd ℂ) (t v)
  let x : mixedEmbedding.mixedSpace E :=
    (0, fun u => if h : ∃ v, u.1 = w v then c h.choose else 0)
  have hmem : x - ZSpan.fract (mixedEmbedding.latticeBasis E) x ∈
      mixedEmbedding.integerLattice E := by
    rw [← mixedEmbedding.mem_span_latticeBasis, ZSpan.fract_apply, sub_sub_cancel]
    exact (ZSpan.floor _ x).2
  obtain ⟨m, hm⟩ := hmem
  have hm' : mixedEmbedding E (m : E) = x - ZSpan.fract (mixedEmbedding.latticeBasis E) x := hm
  refine ⟨m, fun v => ?_⟩
  have hc : (w v).IsComplex := hE.isComplex (w v)
  let u : {u : InfinitePlace E // u.IsComplex} := ⟨w v, hc⟩
  have hxu : x.2 u = c v := by
    have hex : ∃ v', u.1 = w v' := ⟨v, rfl⟩
    show (if h : ∃ v', u.1 = w v' then c h.choose else 0) = c v
    rw [dif_pos hex, hinj _ _ hex.choose_spec.symm]
  have hfr : x - mixedEmbedding E (m : E) = ZSpan.fract (mixedEmbedding.latticeBasis E) x := by
    rw [hm', sub_sub_cancel]
  have hval : (ZSpan.fract (mixedEmbedding.latticeBasis E) x).2 u
      = c v - (w v).embedding (m : E) := by
    rw [← hfr, Prod.snd_sub, Pi.sub_apply, hxu, mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hb : ‖c v - (w v).embedding (m : E)‖ ≤ R := by
    rw [← hval]
    exact ((norm_le_pi_norm _ u).trans (norm_snd_le _)).trans
      (hR _ (ZSpan.fract_mem_fundamentalDomain _ x))
  by_cases h : (w v).embedding = φ v
  · have hcv : c v = t v := if_pos h
    rw [hcv, h] at hb
    exact hb
  · have h2 : (w v).embedding = ComplexEmbedding.conjugate (φ v) :=
      (InfinitePlace.embedding_mk_eq (φ v)).resolve_left h
    have hcv : c v = (starRingEnd ℂ) (t v) := if_neg h
    rw [hcv, h2, ComplexEmbedding.conjugate_coe_eq, ← map_sub, Complex.norm_conj] at hb
    exact hb
end Formalism.L2.SG.Pf
