-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.StepPlus_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:55:31.28127+00:00
-- url     : https://prove2.me/submissions/24c4017d-d905-4f40-b8ab-bd4375aef721

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepPlus
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_sp_midGen_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_sp_gen_P
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_sp_wU_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_sp_xi_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_biHom_plus
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_deg_U
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_span_map_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_tieF_pow_apply_eq_zero_of_min_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_wU_ne_xi


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
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : PairStep → LatPlus → PLLin → CommPL → ParamPL → PlusCondition := by
  intro hPS hLP hLin hComm hPar p _ N r _ D a u hB hr hdeg hBa hz hU hu
  have key : ∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp → ∀ x ∈ Lat p D (r := r) j jp,
      ((p : ℚ_[p]) ^ u • midGen p D 0 j jp x ∈ MidP p (r := r) D) ∧
      ((p : ℚ_[p]) ^ u • ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
        Pplus p D jp (PL p D (List.finRange D.T.t) j jp x)) ∈ Mid p (r := r) D 0) := by
    intro j jp hOK x hx
    obtain ⟨T, hT⟩ := (hLin p N r D (List.finRange D.T.t) j jp).1
    have hcomm : ∀ (m : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
        (tieF (wU D) (xiVar N r D.T.t) ^ m) (T y) = T ((tieF (wU D) (xiVar N r D.T.t) ^ m) y) := by
      intro m y
      rw [hT, hT]
      exact (hComm p N r D hB (List.finRange D.T.t) j jp m y).2
    have hps := hPS p (BVar N r D.T.t) r (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) hr
      (fun c => ⟨by simp [wU, zP, scalZ], by simp [xiVar, zP, scalZ]⟩)
      (D.LL.deg D.uPos) D.B D.zPlus (Nat.log p (2 * a)) u
      (fun l => Submodule.map (T.restrictScalars ℤ_[p]) (Lat p D (r := r) j l))
      (by
        rintro l _ ⟨y, hy, rfl⟩ m hm
        rw [LinearMap.restrictScalars_apply, hcomm]
        have hb := biHom_plus (p := p) (D := D) j l y hy
        rw [deg_U hB] at hb
        rw [tieF_pow_apply_eq_zero_of_min_lt (wU D) (xiVar N r D.T.t) sp_wU_inj sp_xi_inj wU_ne_xi hb m hm, map_zero])
      (by
        rintro l m hm _ ⟨y, hy, rfl⟩
        rw [LinearMap.restrictScalars_apply, hcomm, ← map_smul]
        refine ⟨_, hLP p N r D hB hU j l m (Nat.log p (2 * a)) (Nat.log_mono_right ?_) y hy, rfl⟩
        exact le_trans (le_trans hm (min_le_left _ _)) (hdeg _))
      (by
        refine le_trans (Nat.add_le_add_left (Nat.log_mono_right ?_) _) hu
        have := hdeg D.uPos
        omega)
      jp hOK.2 (T x) ⟨x, hx, rfl⟩
    constructor
    · rw [sp_midGen_zero, ← hT, ← mul_smul_comm]
      refine span_map_mem (LinearMap.mulLeft ℚ_[p] (∏ i, D.Ehat p (r := r) i ^ j i)) _ _ ?_ _ hps.1
      rintro _ ⟨l', hl', _, ⟨y, hy, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨j, l', ⟨hOK.1, hl'⟩, y, hy, ?_⟩
      rw [LinearMap.mulLeft_apply, LinearMap.restrictScalars_apply, hT, sp_gen_P,
        hPar p N r D hB (List.finRange D.T.t) j j jp l' y (fun _ _ => rfl)]
    · rw [sp_gen_P, ← hT, ← mul_smul_comm]
      refine span_map_mem (LinearMap.mulLeft ℚ_[p] (∏ i, D.Ehat p (r := r) i ^ j i)) _ _ ?_ _ hps.2
      rintro _ ⟨l', hl', _, ⟨y, hy, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨j, l', ⟨hOK.1, hl'⟩, y, hy, ?_⟩
      rw [LinearMap.mulLeft_apply, LinearMap.restrictScalars_apply, hT, sp_midGen_zero,
        hPar p N r D hB (List.finRange D.T.t) j j jp l' y (fun _ _ => rfl)]
  let S : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
    (p : ℚ_[p]) ^ u • LinearMap.id
  constructor
  · intro v hv
    refine span_map_mem S _ (MidP p (r := r) D) ?_ v hv
    rintro _ ⟨j, jp, hOK, x, hx, rfl⟩
    exact (key j jp hOK x hx).1
  · intro v hv
    refine span_map_mem S _ (Mid p (r := r) D 0) ?_ v hv
    rintro _ ⟨j, jp, hOK, x, hx, rfl⟩
    exact (key j jp hOK x hx).2
end Formalism.InvariantFactorPaths.KP.LL
