-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:48:32.944367+00:00
-- url     : https://prove2.me/submissions/586f2dba-942f-41c3-98c3-1904c615d96d

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_notin
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_mid_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_mid
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_Q_update
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_wv_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_ev_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_wv_ne_ev
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_levelOK
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_biHom_tie
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_deg_lettersAt_pos
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_deg_lettersAt_pos_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_span_map_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_tieF_pow_apply_eq_zero_of_min_lt


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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
variable {D}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hPS : PairStep) (hLT : LatTie) (hLin : PLLin) (hC : CommPL) (hPar : ParamPL) (a u : ℕ)
    (hB : D.BlockOK) (hr : 1 ≤ r) (hdeg : ∀ x, D.LL.deg x ≤ 2 * a) (hzz : ∀ i, D.T.z i ≤ 2 * a)
    (hH : HypJoin p (r := r) D) (hu : r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u) (k : ℕ) (hk : k < D.T.t)
    (j : Fin D.T.t → ℕ) (jp : ℕ) (hOK : D.LevelOK j jp) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ Lat p D (r := r) j jp) :
    (p : ℚ_[p]) ^ u • midGen p D (k + 1) j jp x ∈ Mid p (r := r) D k ∧
      (p : ℚ_[p]) ^ u • midGen p D k j jp x ∈ Mid p (r := r) D (k + 1) := by
  obtain ⟨T, hT⟩ := (hLin p N r D ((List.finRange D.T.t).drop (k + 1)) j jp).1
  have hnot := st_notin D.T.t k hk
  generalize hkk : (⟨k, hk⟩ : Fin D.T.t) = kk at hnot
  generalize hL' : (List.finRange D.T.t).drop (k + 1) = L' at hnot hT
  let Λ : ℕ → Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) := fun l =>
    Submodule.map (T.restrictScalars ℤ_[p]) (Lat p D (Function.update j kk l) jp)
  have hcomm : ∀ m y, (tieF (wv D kk) (ev D kk) ^ m) (T y) = T ((tieF (wv D kk) (ev D kk) ^ m) y) := by
    intro m y
    rw [hT, hT]
    exact (hC p N r D hB L' j jp m y).1 kk hnot
  have ho := hdeg (D.letterAt (D.T.pos kk))
  have hn := hdeg (D.letterAt (D.T.pos kk + 1))
  have hz' := hzz kk
  have key := hPS p (BVar N r D.T.t) r (wv D kk) (ev D kk) (zi D r kk) (si D r kk) hr
    (fun c => ⟨Sum.inl_ne_inr, Sum.inl_ne_inr⟩)
    (D.LL.deg (D.letterAt (D.T.pos kk))) (D.LL.deg (D.letterAt (D.T.pos kk + 1))) (D.T.z kk)
    (Nat.log p (2 * a)) u Λ
    (by
      rintro l x' ⟨x'', hx'', rfl⟩ m hm
      show (tieF (wv D kk) (ev D kk) ^ m) (T x'') = 0
      have hb := biHom_tie hB (Function.update j kk l) jp kk x'' hx''
      rw [deg_lettersAt_pos hB, deg_lettersAt_pos_succ hB, Function.update_self] at hb
      rw [hcomm, tieF_pow_apply_eq_zero_of_min_lt (wv D kk) (ev D kk) (st_wv_inj kk) (st_ev_inj kk) (st_wv_ne_ev hB kk) hb m hm,
        map_zero])
    (by
      rintro l m hm x' ⟨x'', hx'', rfl⟩
      have h := hLT p N r D hB hH (Function.update j kk l) jp kk m (Nat.log p (2 * a))
        (Nat.log_mono_right (le_trans hm (le_trans (min_le_left _ _) ho))) x'' hx''
      have he : Function.update j kk l + Pi.single kk m = Function.update j kk (l + m) := by
        funext i
        by_cases hi : i = kk
        · subst hi; simp
        · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
      rw [he] at h
      refine ⟨_, h, ?_⟩
      show T _ = _ • (tieF (wv D kk) (ev D kk) ^ m) (T x'')
      rw [map_smul, hcomm])
    (le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu)
    (j kk) (le_min (hOK.1 kk).1 (hOK.1 kk).2) (T x)
    ⟨x, by rw [Function.update_eq_self]; exact hx, rfl⟩
  subst hkk
  subst hL'
  constructor
  · have := span_map_mem (LinearMap.mulLeft ℚ_[p] (stQ p D k ⟨k, hk⟩ j jp)) _ (Mid p (r := r) D k) ?_ _ key.1
    · rw [st_mid_succ p k hk, ← hT, ← mul_smul_comm]
      exact this
    · rintro v ⟨l', hl', x', ⟨x'', hx'', rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨Function.update j ⟨k, hk⟩ l', jp, st_levelOK _ j jp l' hOK hl', x'', hx'', ?_⟩
      rw [st_mid p hB k hk, st_Q_update, Function.update_self,
        hPar p N r D hB _ (Function.update j ⟨k, hk⟩ l') j jp jp x''
          (fun i hi => Function.update_of_ne (fun h : i = ⟨k, hk⟩ => hnot (h ▸ hi)) _ _), ← hT]
      rfl
  · have := span_map_mem (LinearMap.mulLeft ℚ_[p] (stQ p D k ⟨k, hk⟩ j jp)) _ (Mid p (r := r) D (k + 1)) ?_ _ key.2
    · rw [st_mid p hB k hk, ← hT, ← mul_smul_comm]
      exact this
    · rintro v ⟨l', hl', x', ⟨x'', hx'', rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨Function.update j ⟨k, hk⟩ l', jp, st_levelOK _ j jp l' hOK hl', x'', hx'', ?_⟩
      rw [st_mid_succ p k hk, st_Q_update, Function.update_self,
        hPar p N r D hB _ (Function.update j ⟨k, hk⟩ l') j jp jp x''
          (fun i hi => Function.update_of_ne (fun h : i = ⟨k, hk⟩ => hnot (h ▸ hi)) _ _), ← hT]
      rfl
end Formalism.InvariantFactorPaths.KP.LL
