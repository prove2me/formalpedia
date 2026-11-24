-- Prove2me | solution 1 for Formalism.CountingSumsFrames.phi_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:05.207378+00:00
-- url     : https://prove2.me/submissions/486411ef-8903-4f67-a608-c8ed8bec5ed0

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_phi_mem
import Theorems.Thm_Formalism_CountingSumsFrames_pol_iff_eul
import Theorems.Thm_Formalism_CountingSumsFrames_eulL_E_pow
import Theorems.Thm_Formalism_GM_FockB_eulL_mem
import Theorems.Thm_Formalism_GM_FockB_ops_apply_comm
import Theorems.Thm_Formalism_GM_ProjS_eulL_e_S_mul
import Theorems.Thm_Formalism_GM_ProjS_eulL_tieF_pow
import Theorems.Thm_Formalism_GM_ProjS_eulL_w_S_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (j : Fin T.t) (h : T.pos j + 1 < N) :
    ∀ x ∈ Pol p r LL, T.phi p LL j x ∈ Pol p r LL := by
  intro x hx
  rw [pol_iff_eul] at hx ⊢
  intro i
  set a : Fin N := ⟨T.pos j, by omega⟩ with ha
  set b : Fin N := ⟨T.pos j + 1, h⟩ with hb
  have hab : a ≠ b := by intro h'; have := congrArg Fin.val h'; simp [a, b] at this
  have hw : Function.Injective (fun c : Fin r => (a, c)) := fun c d h' => (Prod.mk.inj h').2
  have he : Function.Injective (fun c : Fin r => (b, c)) := fun c d h' => (Prod.mk.inj h').2
  have hwe : ∀ c d : Fin r, (a, c) ≠ (b, d) := fun c d h' => hab (Prod.mk.inj h').1
  have hphi : T.phi p LL j = tiePhi (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (LL.deg a) (LL.deg b) (T.z j) := by
    unfold TieData.phi; rw [dif_pos h]; rfl
  by_cases hia : i = a
  · subst hia
    rw [hphi]
    unfold tiePhi
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_smul]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm]
    congr 1
    have hF := ProjS.eulL_tieF_pow (fun c : Fin r => (a, c)) hw (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))
      (fun c => Or.inl ⟨⟨c, rfl⟩, fun d h' => hwe d c h'⟩) x _ (hx a) l
    have hE := eulL_E_pow (fun c : Fin r => (a, c)) (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))
      (fun g α hg => ProjS.eulL_w_S_mul hw hwe g α hg) _ _ hF l
    rw [hE]; congr 1; ring
  by_cases hib : i = b
  · subst hib
    rw [hphi]
    unfold tiePhi
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_smul]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm]
    congr 1
    have hF := ProjS.eulL_tieF_pow (fun c : Fin r => (b, c)) he (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))
      (fun c => Or.inr ⟨fun d h' => hwe c d h'.symm, ⟨c, rfl⟩⟩) x _ (hx b) l
    have hE := eulL_E_pow (fun c : Fin r => (b, c)) (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))
      (fun g α hg => ProjS.eulL_e_S_mul he hwe g α hg) _ _ hF l
    rw [hE]; congr 1; ring
  · have hdisj : Disjoint {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} {v | v.1 = i} := by
      rw [Set.disjoint_left]
      rintro v hv1 hv2
      simp only [Set.mem_ofPred_eq] at hv1 hv2
      rcases hv1 with h1 | h1
      · exact hia (by rw [← hv2]; exact Fin.ext h1)
      · exact hib (by rw [← hv2]; exact Fin.ext h1)
    have hc := FockB.ops_apply_comm hdisj (phi_mem LL T j h)
      (FockB.eulL_mem (S := {v : Fin N × Fin r | v.1 = i}) (fun c : Fin r => (i, c)) (fun c => rfl)) x
    rw [← hc, hx i, map_smul]
end Formalism.CountingSumsFrames
