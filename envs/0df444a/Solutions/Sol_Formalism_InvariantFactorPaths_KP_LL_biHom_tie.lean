-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.biHom_tie
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:49.122799+00:00
-- url     : https://prove2.me/submissions/64774739-2759-4f1a-b260-9f2daa284e43

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_BiHomPlus
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_wv_ne_xi
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_ev_ne_xi
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_yz_pol
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_biHom_span
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_chainEmb_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_ev_chain
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_supp_gen
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_wv_chain
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_xi_supp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    ∀ x ∈ Lat p D (r := r) j jp, BiHom (wv D i) (ev D i) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i)))
      ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1))) x := by
  intro x hx
  refine biHom_span (S := {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}) ?_ x hx
  rintro _ ⟨y, hy, g, hg, rfl⟩ m hm
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_gen (p := p) (D := D) (hm := hm)
  have hdeg : MultiDeg (D.lettersAt j jp) m1 :=
    ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 (yz_pol hy)) hm1
  have hxi := (xi_supp (p := p) (D := D) (hg := hg) (hm2 := hm2))
  constructor
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (wv D i c) = m1 (D.letterAt (D.T.pos i), c) := fun c => by
      rw [wv_chain (hB := hB), Finsupp.mapDomain_apply (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (wv D i c) = 0 := fun c => hxi.1 _ (fun d => wv_ne_xi hB i c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (ev D i c) = m1 (D.letterAt (D.T.pos i + 1), c) := fun c => by
      rw [ev_chain (hB := hB), Finsupp.mapDomain_apply (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (ev D i c) = 0 := fun c => hxi.1 _ (fun d => ev_ne_xi hB i c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _
end Formalism.InvariantFactorPaths.KP.LL
