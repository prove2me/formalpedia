-- Prove2me | solution 1 for Formalism.L2.Pj.wtAll_of_borChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:16:56.259294+00:00
-- url     : https://prove2.me/submissions/6873dd0a-d502-4577-9d85-b8fcec2557de

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
import Theorems.Thm_Formalism_L2_Pj_chartAt_val
import Theorems.Thm_Formalism_L2_Pj_eq_of_locM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Pj
section Charts
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {pts mapR borR}
private theorem evalAt_spec_lemma {f : Rules pts} {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : ∃ (p : TRing K) (φ : p.R →ₐ[K] S) (y0 : pts p.R),
      mapR φ y0 y ∧ evalAt pts mapR f y = φ (f p y0) := by
  refine ⟨hy.choose, hy.choose_spec.choose, hy.choose_spec.choose_spec.choose,
    hy.choose_spec.choose_spec.choose_spec, ?_⟩
  rw [evalAt, dif_pos hy]
end Charts
end Formalism.L2.Pj
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {pts mapR borR}
namespace Formalism.L2.Pj
theorem _root_.solution [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℕ) {f : Rules pts}
    (hf : IsNatural pts mapR f) (hw : IsWeight pts borR e f) (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = wchar e t * evalAt pts mapR f y := by
  obtain ⟨p, φ, y0, hm, hv⟩ := evalAt_spec_lemma (f := f) hy
  obtain ⟨p', φ', y0', hm', hv'⟩ := evalAt_spec_lemma (f := f) hy'
  rw [hv, hv']
  apply eq_of_locM (K := K)
  intro m hmax
  haveI := hmax
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hm', chartAt_val hf hc hm]
  calc c' (f A u) = (cB.comp π') (f A u) := by rw [e2]
    _ = cB (f B uB') := by rw [AlgHom.comp_apply, hf A B π' u uB' hπ']
    _ = cB (wchar e tB) * cB (f B uB) := by rw [hw B tB uB uB' hbB, map_mul]
    _ = locM K m (wchar e t) * c (f A u) := by
      have k1 : cB (f B uB) = c (f A u) := by rw [← e1, AlgHom.comp_apply, hf A B π u uB hπ]
      rw [k1]
      simp [wchar, map_prod, map_pow, e3, Units.coe_prod]
end Formalism.L2.Pj
