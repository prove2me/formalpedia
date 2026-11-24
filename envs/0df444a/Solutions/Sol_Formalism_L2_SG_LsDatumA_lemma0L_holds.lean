-- Prove2me | solution 1 for Formalism.L2.SG.LsDatumA.lemma0L_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:25:06.671442+00:00
-- url     : https://prove2.me/submissions/38a4494f-1dd3-40c3-806b-fad4da80ce83

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_LinQRawRange
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LsDatumA
import Theorems.Thm_Formalism_L2_SG_LsDatumA_sub_mem_X_of_mkW_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.LsDatumA
open Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
namespace Formalism.L2.SG.LsDatumA
theorem _root_.solution (M : Model F E) (r : ℕ) : Lemma0L M r := by
  intro hsplit V _ _ H t hgen w hw
  classical
  have hprim := hgen.2
  simp only [HermSp.MMfam, hsplit] at hprim
  obtain ⟨hmem, hli, hspan⟩ := hprim
  constructor
  · intro hwL
    exact ⟨⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, rfl⟩, ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, hwL, rfl⟩⟩
  · rintro ⟨⟨x, hxL, hxw⟩, ⟨x', hx'L, hx'w⟩⟩
    have hp : (x : V) - w ∈ Submodule.span E (Set.range fun a : Fin r => t.f a.castSucc) :=
      sub_mem_X_of_mkW_eq H (y := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩) hxw
    have hq : (x' : V) - w ∈ Submodule.span E (Set.range fun a : Fin r => t.f' a.castSucc) :=
      sub_mem_X_of_mkW_eq H (y := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩) hx'w
    obtain ⟨cp, hcp⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hp
    obtain ⟨cq, hcq⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hq
    have hdiff : (x : V) - x' ∈ t.abelian₂ := t.abelian₂.sub_mem hxL hx'L
    have hdiffE : (x : V) - x' ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
      have e : (x : V) - x' = ((x : V) - w) - ((x' : V) - w) := by abel
      rw [e]
      refine Submodule.sub_mem _ ?_ ?_
      · exact (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a.castSucc, rfl⟩)) hp
      · exact (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a.castSucc, rfl⟩)) hq
    obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan _ hdiff hdiffE)
    have hinjl : Function.Injective (fun a : Fin r => (Sum.inl a.castSucc : Fin (r + 1) ⊕ Fin (r + 1))) :=
      Sum.inl_injective.comp (Fin.castSucc_injective r)
    have hinjr : Function.Injective (fun a : Fin r => (Sum.inr a.castSucc : Fin (r + 1) ⊕ Fin (r + 1))) :=
      Sum.inr_injective.comp (Fin.castSucc_injective r)
    set e1 : (Fin (r + 1) ⊕ Fin (r + 1)) →₀ E :=
      cp.mapDomain (fun a => Sum.inl a.castSucc) - cq.mapDomain (fun a => Sum.inr a.castSucc) with he1
    set e2 : (Fin (r + 1) ⊕ Fin (r + 1)) →₀ E := l.mapRange (fun a : M.L.O => (a : E)) rfl with he2
    have h1 : Finsupp.linearCombination E (Sum.elim t.f t.f') e1 = (x : V) - x' := by
      rw [he1, map_sub, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_mapDomain,
        Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
      have e : (x : V) - x' = ((x : V) - w) - ((x' : V) - w) := by abel
      rw [e, ← hcp, ← hcq]
      rfl
    have h2 : Finsupp.linearCombination E (Sum.elim t.f t.f') e2 = (x : V) - x' := by
      rw [← hl, he2, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
      rfl
    have he : e1 = e2 := hli (h1.trans h2.symm)
    have hcoef : ∀ a : Fin r, cp a = (l (Sum.inl a.castSucc) : E) := by
      intro a
      have h := congrArg (fun e => e (Sum.inl a.castSucc)) he
      simp only [he1, he2, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply] at h
      rw [Finsupp.mapDomain_apply hinjl, Finsupp.mapDomain_notin_range _ _ (by
        rintro ⟨b, hb⟩
        simp at hb), sub_zero] at h
      exact h
    have hpL : (x : V) - w ∈ t.abelian₂ := by
      rw [← hcp]
      refine Submodule.sum_mem _ fun a _ => ?_
      rw [hcoef a]
      exact t.abelian₂.smul_mem (l (Sum.inl a.castSucc)) (hmem (Sum.inl a.castSucc))
    have e : w = (x : V) - ((x : V) - w) := by abel
    rw [e]
    exact t.abelian₂.sub_mem hxL hpL
end Formalism.L2.SG.LsDatumA
